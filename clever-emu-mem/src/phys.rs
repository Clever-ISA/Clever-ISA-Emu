use std::alloc::{alloc_zeroed, Layout};

use std::cell::SyncUnsafeCell;
use std::collections::HashMap;

use bytemuck::{Pod, Zeroable};
use clever_emu_primitives::const_zeroed_safe;
use clever_emu_primitives::primitive::{LeU32, LeU64};

use parking_lot::RwLock;
use parking_lot_core::{park, unpark_filter, FilterOp, ParkToken, UnparkToken};

use crate::cache::{CacheAccessError, CacheFetch, CacheInvalidate, CacheLine, CacheWrite, Status};

#[derive(Debug, Clone, Copy, Zeroable, Pod)]
#[repr(C, align(4096))]
pub struct Page([u8; 4096]);

impl Page {
    pub const SIZE: i64 = core::mem::size_of::<Self>() as i64;

    pub const ZERO_PAGE: &Page = &const_zeroed_safe();
}

#[derive(Debug)]
pub struct SysMemory {
    page_limit: u32,
    // SAFETY:
    // page_count is synchronized by the `pages` lock despite not being directly covered by it.
    // It is sound to perform read accesses to this cell from a thread that owns a shared read lock to `pages` or the exclusive write lock to `pages`
    // It is sound to perform write accesses to this cell from a thread that owns the excusive write lock to `pages`
    page_count: SyncUnsafeCell<u32>,
    pages: RwLock<HashMap<LeU32, RwLock<Box<Page>>>>,
}

impl SysMemory {
    pub fn new(page_limit: u32) -> Self {
        Self {
            page_limit,
            page_count: SyncUnsafeCell::new(0),
            pages: RwLock::new(HashMap::new()),
        }
    }

    fn allocate_if_absent(&self, page: LeU32) -> Result<(), CacheAccessError> {
        let lock = self.pages.read();

        if lock.contains_key(&page) {
            Ok(())
        } else {
            drop(lock);
            let mut lock = self.pages.write();

            if unsafe { *self.page_count.get() } >= self.page_limit {
                return Err(CacheAccessError::NoMem);
            }

            unsafe { *self.page_count.get() += 1 };

            let layout = Layout::new::<Page>();
            let bytes = unsafe { alloc_zeroed(layout) };
            if bytes.is_null() {
                return Err(CacheAccessError::NoMem);
            }

            let data = RwLock::new(unsafe { Box::from_raw(bytes.cast()) });

            lock.insert(page, data);

            Ok(())
        }
    }

    /// Directively accesses a given page by
    pub fn with_page(&self, page: LeU32, f: impl FnOnce(&Page)) -> Result<(), CacheAccessError> {
        self.allocate_if_absent(page)?;
        let lock = self.pages.read();

        let lock = lock[&page].read();

        f(&lock);

        Ok(())
    }

    pub fn with_page_mut(
        &self,
        page: LeU32,
        f: impl FnOnce(&mut Page),
    ) -> Result<(), CacheAccessError> {
        self.allocate_if_absent(page)?;
        let lock = self.pages.read();

        let mut lock = lock[&page].write();

        f(&mut lock);

        Ok(())
    }
}

impl CacheInvalidate for SysMemory {
    fn invalidate(&self, _: LeU64) {}

    fn invalidate_all(&self) {}
}

impl CacheFetch for SysMemory {
    fn probe_on_miss_only(&self) -> bool {
        true
    }

    fn probe_attrs(
        &self,
        line: LeU64,
    ) -> crate::cache::CacheAccessResult<crate::cache::CacheAttrs> {
        todo!()
    }

    fn read_line(&self, line: LeU64) -> crate::cache::CacheAccessResult<crate::cache::CacheLine> {
        let page = (line >> 12).truncate_to();
        let page_offset = (line & 0x3C0).get() as usize;

        self.allocate_if_absent(page)?;
        let lock = self.pages.read();

        let pg = &lock[&page];

        let lock = pg.read();

        let line = &lock.0[page_offset..][..core::mem::size_of::<CacheLine>()];

        let mut output = CacheLine::zeroed();

        bytemuck::bytes_of_mut(&mut output).copy_from_slice(line);

        Ok((output, Status::Hit))
    }

    fn park_on_line_unlock(&self, line: LeU64) {
        let page = (line >> 12).truncate_to();

        let lock = self.pages.read();

        let pg = &lock[&page];

        let lock = pg.read();

        let addr = core::ptr::addr_of!(lock.0).addr();

        unsafe {
            park(
                addr,
                || true,
                || (),
                |_, _| (),
                ParkToken(line.get() as usize),
                None,
            );
        }
    }
}

impl CacheWrite for SysMemory {
    fn write_line(&self, line: LeU64, val: CacheLine) -> crate::cache::CacheAccessResult<()> {
        let page = (line >> 12).truncate_to();

        let page_offset = (line & 0x3C0).get() as usize;

        self.allocate_if_absent(page)?;

        let lock = self.pages.read();

        let pg = &lock[&page];

        let mut lock = pg.write();

        let line = &mut lock.0[page_offset..][..core::mem::size_of::<CacheLine>()];

        line.copy_from_slice(bytemuck::bytes_of(&val));

        Ok(((), Status::Hit))
    }

    fn lock(&self, _: LeU64) -> crate::cache::CacheAccessResult<()> {
        Ok(((), Status::Hit))
    }

    fn unlock(&self, line: LeU64) -> crate::cache::CacheAccessResult<()> {
        let page = (line >> 12).truncate_to();

        self.allocate_if_absent(page)?;

        let lock = self.pages.read();

        let pg = &lock[&page];

        let lock = pg.write();

        let addr = core::ptr::addr_of!(lock.0).addr();

        unsafe {
            unpark_filter(
                addr,
                |tok| {
                    if tok.0 == line.get() as usize {
                        FilterOp::Unpark
                    } else {
                        FilterOp::Skip
                    }
                },
                |_| UnparkToken(line.get() as usize),
            );
        }

        Ok(((), Status::Hit))
    }
}
