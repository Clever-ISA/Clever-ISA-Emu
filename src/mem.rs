use std::{
    alloc::Layout,
    cell::{Cell, RefCell, UnsafeCell},
    collections::{
        hash_map::{DefaultHasher, RandomState},
        HashMap, HashSet,
    },
    f32::consts::E,
    hash::{BuildHasher, Hash, Hasher},
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::{atomic::AtomicUsize, Arc},
};

use bytemuck::{Pod, Zeroable};

use lccc_siphash::SipHasher;
use lru_time_cache::LruCache;
use parking_lot::{Condvar, Mutex, RwLock, RwLockReadGuard};
use rand::Rng;

use crate::{
    bitfield::bitfield,
    error::{AccessKind, CPUException, CPUResult, FaultCharacteristics, FaultStatus},
    primitive::*,
    util::Racy,
};

#[repr(C, align(4096))]
#[derive(Copy, Clone, Hash, Zeroable, Pod)]
pub struct Page([u8; 4096]);

pub struct MemoryParker {
    base: Mutex<u32>,
    var: Condvar,
}

impl MemoryParker {
    pub fn new() -> Self {
        Self {
            base: Mutex::new(0),
            var: Condvar::new(),
        }
    }

    pub fn park(&self) {
        let mut guard = self.base.lock();
        if let Some(val) = guard.checked_sub(1) {
            *guard = val;
            return;
        }
        self.var.wait(&mut guard);
    }

    pub fn unpark(&self) {
        let mut guard = self.base.lock();
        if self.var.notify_all() == 0 {
            *guard += 1;
        }
    }
}

pub struct MemoryController {
    mem: RwLock<HashMap<LeU32, Box<UnsafeCell<Page>>>>,
    mem_parkers: RwLock<HashMap<LeU32, MemoryParker>>,
    memlock: RwLock<()>,
    gen_counter: Mutex<lccc_siphash::SipHasher<2, 4>>,
    memory_cap: usize,
    memory_allocated: Racy<Cell<usize>>,
    has_used: RwLock<HashSet<(LeU64, LeU64)>>,
}

impl MemoryController {
    fn allocate(
        &self,
        htab: &mut HashMap<LeU32, Box<UnsafeCell<Page>>>,
        page: LeU32,
        mut base_chars: FaultCharacteristics,
    ) -> CPUResult<()> {
        // Safety: `htab` is inside an exclusively borrowed rwlock
        let mem_alloced = unsafe { self.memory_allocated.get() };

        if mem_alloced.get() == self.memory_cap {
            base_chars.access_kind = AccessKind::Allocate;
            return Err(CPUException::PageFault(
                (page.unsigned_as::<LeI64>()) << 12,
                base_chars,
            ));
        }

        // SAFETY: size_of::<Page>()==4096
        let ptr = unsafe { std::alloc::alloc_zeroed(Layout::new::<Page>()) };

        if ptr.is_null() {
            base_chars.access_kind = AccessKind::Allocate;
            Err(CPUException::PageFault(
                (page.unsigned_as::<LeI64>()) << 12,
                base_chars,
            ))
        } else {
            mem_alloced.set(mem_alloced.get() + 1);
            // SAFETY: Page is allocated using the global allocator above
            // ptr is not null be by the above check
            // and ptr is not used after this point
            let ptr = unsafe { Box::from_raw(ptr.cast()) };

            htab.insert(page, ptr);
            Ok(())
        }
    }
    fn allocate_page_if_absent(
        &self,
        page: LeU32,
        base_chars: FaultCharacteristics,
    ) -> CPUResult<RwLockReadGuard<HashMap<LeU32, Box<UnsafeCell<Page>>>>> {
        let mem = self.mem.read();
        if !mem.contains_key(&page) {
            drop(mem);
            let mut gmem = self.mem.write();

            if !gmem.contains_key(&page) {
                let mut parkers = self.mem_parkers.write();
                self.allocate(&mut gmem, page, base_chars)?;

                parkers.insert(page, MemoryParker::new());
            }

            drop(gmem);
            Ok(self.mem.read())
        } else {
            Ok(mem)
        }
    }

    pub fn new(memory_cap: usize) -> Self {
        let mut rand = rand::thread_rng();
        Self {
            mem: RwLock::new(HashMap::new()),
            memlock: RwLock::new(()),
            gen_counter: Mutex::new(SipHasher::new_with_keys(rand.gen(), rand.gen())),
            memory_cap,
            memory_allocated: Racy::new(Cell::new(0)),
            has_used: RwLock::new(HashSet::new()),
            mem_parkers: RwLock::new(HashMap::new()),
        }
    }

    fn write_bytes_single_page(
        &self,
        bytes: &[u8],
        paddr: LeU64,
        mut base_chars: FaultCharacteristics,
    ) -> CPUResult<()> {
        base_chars.status |= FaultStatus::with_non_canonical(true);
        base_chars.access_kind = AccessKind::Allocate;
        if paddr > 0xFFFFFFFF {
            return Err(CPUException::PageFault(paddr.cast_sign(), base_chars));
        }

        let (page, offset) = (paddr >> 12, paddr & 0xFFF);

        let page = page.truncate_to::<LeU32>();

        let offset = offset.get() as usize;

        let mem = self.allocate_page_if_absent(page, base_chars)?;

        let write_lock = self.memlock.write();

        let page = mem.get(&page).unwrap();

        let page = unsafe { &mut (*page.get()).0 };

        let page_bytes = &mut page[offset..][..bytes.len()];

        page_bytes.copy_from_slice(bytes);

        Ok(())
    }

    fn read_bytes_single_page(
        &self,
        bytes: &[u8],
        paddr: LeU64,
        mut base_chars: FaultCharacteristics,
    ) -> CPUResult<()> {
        base_chars.status |= FaultStatus::with_non_canonical(true);
        base_chars.access_kind = AccessKind::Allocate;
        if paddr > 0xFFFFFFFF {
            return Err(CPUException::PageFault(paddr.cast_sign(), base_chars));
        }

        let (page, offset) = (paddr >> 12, paddr & 0xFFF);

        let page = page.truncate_to::<LeU32>();

        let offset = offset.get() as usize;

        let mem = self.allocate_page_if_absent(page, base_chars)?;

        let read_lock = self.memlock.read();

        let page = mem.get(&page).unwrap();

        let page = unsafe { &(*page.get()).0 };

        let page_bytes = &page[offset..][..bytes.len()];

        Ok(())
    }

    pub fn write_memory_aligned(
        &self,
        bytes: &[u8],
        paddr: LeU64,
        base_chars: FaultCharacteristics,
    ) -> CPUResult<()> {
        let alignment = bytes.len().next_power_of_two().max(4096);

        if (paddr & (alignment as u64 - 1)) != 0 {
            panic!("Unaligned access to `write_memory_aligned` {:#x}", paddr)
        }

        for slice in bytes.chunks(4096) {
            self.write_bytes_single_page(slice, paddr, base_chars)?;
        }

        Ok(())
    }

    pub fn read_memory_aligned(
        &self,
        bytes: &mut [u8],
        paddr: LeU64,
        base_chars: FaultCharacteristics,
    ) -> CPUResult<()> {
        let alignment = bytes.len().next_power_of_two().max(4096);

        if (paddr & (alignment as u64 - 1)) != 0 {
            panic!("Unaligned access to `write_memory_aligned` {:#x}", paddr)
        }

        for slice in bytes.chunks(4096) {
            self.read_bytes_single_page(slice, paddr, base_chars)?;
        }

        Ok(())
    }
}

impl CacheInvalidate for MemoryController {
    fn invalidate(&self, _: LeU64) {}

    fn invalidate_all(&self) {}
}

impl CacheFetch for MemoryController {
    fn probe_on_miss_only(&self) -> bool {
        true
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        let mut gen_counter = self.gen_counter.lock();

        line.hash(&mut *gen_counter);

        let seq_lock = gen_counter.finish() & !0xFFFF;
        drop(gen_counter);

        Ok((
            CacheAttrs {
                seq_lock: LeU64::new(seq_lock),
            },
            Status::Hit,
        ))
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        let mut line = CacheLine::zeroed();

        self.read_memory_aligned(
            bytemuck::bytes_of_mut(&mut line),
            val << 6,
            FaultCharacteristics::zeroed(),
        )
        .map_err(CacheAccessError::Exception)?;

        Ok((line, Status::Hit))
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        let page = (line >> 6).truncate_to();
        let guard = self.mem_parkers.read();
        if let Some(parker) = guard.get(&page) {
            parker.park();
        }
    }
}

impl CacheWrite for MemoryController {
    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        self.write_memory_aligned(
            bytemuck::bytes_of(&val),
            line << 6,
            FaultCharacteristics::zeroed(),
        )
        .map_err(CacheAccessError::Exception)?;

        Ok(((), Status::Hit))
    }

    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        Ok(((), Status::Hit))
    }

    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        let page = (line >> 6).truncate_to();
        let guard = self.mem_parkers.read();

        if let Some(parker) = guard.get(&page) {
            parker.unpark();
        }
        Ok(((), Status::Hit))
    }
}

#[repr(C, align(64))]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
pub struct CacheLine([u8; 64]);

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum CacheAccessError {
    Exception(CPUException),
    Locked,
    NotOwned,
}

impl From<CPUException> for CacheAccessError {
    fn from(ex: CPUException) -> Self {
        Self::Exception(ex)
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Status {
    Hit,
    Miss,
}

impl core::ops::BitAnd for Status {
    type Output = Status;
    fn bitand(self, other: Self) -> Self {
        match (self, other) {
            (Self::Hit, Self::Hit) => Self::Hit,
            _ => Self::Miss,
        }
    }
}

pub type CacheAccessResult<T> = Result<(T, Status), CacheAccessError>;

#[repr(C, align(8))]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
pub struct CacheAttrs {
    seq_lock: LeU64,
}

impl CacheAttrs {
    pub const fn is_locked(&self) -> bool {
        (self.seq_lock.get() & 1) != 0
    }
}

pub trait CacheInvalidate {
    fn invalidate(&self, line: LeU64);
    fn invalidate_all(&self);
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for &T {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for &mut T {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for Arc<T> {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for Rc<T> {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for Box<T> {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

pub trait CacheFetch {
    fn probe_on_miss_only(&self) -> bool {
        false
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs>;

    fn read_line(&self, line: LeU64) -> CacheAccessResult<CacheLine>;

    fn park_on_line_unlock(&self, line: LeU64);
}

pub trait CacheWrite: CacheFetch {
    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()>;
    fn lock(&self, line: LeU64) -> CacheAccessResult<()>;
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()>;
}

impl<T: CacheFetch + ?Sized> CacheFetch for &T {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }

    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for &T {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

impl<T: CacheFetch + ?Sized> CacheFetch for Arc<T> {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for Arc<T> {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

impl<T: CacheFetch + ?Sized> CacheFetch for Rc<T> {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for Rc<T> {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

impl<T: CacheFetch + ?Sized> CacheFetch for Box<T> {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for Box<T> {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

impl<T: CacheFetch + ?Sized> CacheFetch for &mut T {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for &mut T {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

pub struct Cache(LruCache<LeU64, (CacheLine, CacheAttrs)>);

impl Cache {
    pub fn new(size: usize) -> Self {
        Self(LruCache::with_capacity(size))
    }

    pub fn invalidate_local(&mut self, line: LeU64) {
        self.0.remove(&line);
    }

    pub fn invalidate_all_local(&mut self) {
        self.0.clear();
    }

    pub fn invalidate_global<C: CacheInvalidate + ?Sized>(&mut self, line: LeU64, upstream: &C) {
        self.invalidate_local(line);
        upstream.invalidate(line);
    }

    pub fn invalidate_all_global<C: CacheInvalidate + ?Sized>(&mut self, upstream: &C) {
        self.invalidate_all_local();
        upstream.invalidate_all()
    }

    pub fn probe_attrs<C: CacheFetch + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<CacheAttrs> {
        if let Some((_, attrs)) = self.0.get(&line) {
            if upstream.probe_on_miss_only() {
                Ok((*attrs, Status::Hit))
            } else {
                let (new_attrs, _) = upstream.probe_attrs(line)?;
                if attrs.seq_lock == (new_attrs.seq_lock & !1) {
                    Ok((*attrs, Status::Hit))
                } else if new_attrs.seq_lock & 1 != 0 {
                    Err(CacheAccessError::Locked)
                } else {
                    let (val, _) = upstream.read_line(line)?;
                    self.0.insert(line, (val, new_attrs));

                    Ok((new_attrs, Status::Miss))
                }
            }
        } else {
            let (attrs, _) = upstream.probe_attrs(line)?;
            if attrs.seq_lock & 1 != 0 {
                Err(CacheAccessError::Locked)
            } else {
                let (val, _) = upstream.read_line(line)?;
                self.0.insert(line, (val, attrs));

                Ok((attrs, Status::Miss))
            }
        }
    }

    pub fn read_line_without_probe<C: CacheFetch + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<CacheLine> {
        if let Some((line, _)) = self.0.get(&line) {
            Ok((*line, Status::Hit))
        } else {
            self.read_line(line, upstream)
        }
    }

    pub fn read_line<C: CacheFetch + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<CacheLine> {
        let (_, status) = self.probe_attrs(line, upstream)?; // we don't need to know the attrs, but this fetches from upstream when needed.

        let (line, _) = self
            .0
            .get(&line)
            .expect("We just probed this line, what do you mean we don't have it's content");

        Ok((*line, status))
    }

    pub fn write_line<C: CacheWrite + ?Sized>(
        &mut self,
        line: LeU64,
        val: CacheLine,
        upstream: &C,
    ) -> CacheAccessResult<()> {
        let (attrs, status) = self.probe_attrs(line, upstream)?;
        if (attrs.seq_lock & 1) == 0 {
            return Err(CacheAccessError::NotOwned);
        }
        let (line_val, _) = self
            .0
            .get_mut(&line)
            .expect("We just probed this line, what do you mean we don't have it's content");

        *line_val = val;

        upstream.write_line(line, val)?;

        Ok(((), status))
    }

    pub fn lock<C: CacheWrite + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<()> {
        let (mut attrs, status) = self.probe_attrs(line, upstream)?;

        if (attrs.seq_lock & 1) == 0 {
            upstream.lock(line)?;
            attrs.seq_lock |= 1;
            let (_, line_attrs) = self
                .0
                .get_mut(&line)
                .expect("We just probed this line, what do you mean we don't have it's content");
            *line_attrs = attrs;
            Ok(((), status))
        } else {
            Err(CacheAccessError::Locked)
        }
    }

    pub fn unlock<C: CacheWrite + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<()> {
        let (mut attrs, status) = self.probe_attrs(line, upstream)?;

        if (attrs.seq_lock & 1) == 1 {
            upstream.unlock(line)?;
            attrs.seq_lock += 1;
            let (_, line_attrs) = self
                .0
                .get_mut(&line)
                .expect("We just probed this line, what do you mean we don't have it's content");
            *line_attrs = attrs;
            Ok(((), status))
        } else {
            Err(CacheAccessError::NotOwned)
        }
    }
}

pub struct MemoryBus {
    mem: MemoryController,
    l3cache: Mutex<Cache>,
}

impl MemoryBus {
    /// Creates a new owning [`MemoryBus`], that can allocate at most `memory_cap` pages and has a l3 cache size specified by `l3size` (in 64 byte cache lines).
    ///
    pub fn new(memory_cap: usize, l3size: usize) -> Self {
        Self {
            mem: MemoryController::new(memory_cap),
            l3cache: Mutex::new(Cache::new(l3size)),
        }
    }
}

impl CacheInvalidate for MemoryBus {
    fn invalidate(&self, line: LeU64) {
        self.l3cache.lock().invalidate_local(line) // We could call `invalidate_global` here, but we know that we'd just be calling `invalidate` on `MemoryController`, so we frankly don't care.
    }

    fn invalidate_all(&self) {
        self.l3cache.lock().invalidate_all_local()
    }
}

impl CacheFetch for MemoryBus {
    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        self.l3cache.lock().probe_attrs(line, &self.mem)
    }

    fn read_line(&self, line: LeU64) -> CacheAccessResult<CacheLine> {
        self.l3cache.lock().read_line(line, &self.mem)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        self.mem.park_on_line_unlock(line)
    }
}

impl CacheWrite for MemoryBus {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        self.l3cache.lock().lock(line, &self.mem)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        self.l3cache.lock().unlock(line, &self.mem)
    }
    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        self.l3cache.lock().write_line(line, val, &self.mem)
    }
}

pub struct LocalMemory<M> {
    shared: M,
    l2cache: RefCell<Cache>,
}

impl<M> LocalMemory<M> {
    pub fn new(shared: M, l2size: usize) -> Self {
        Self {
            shared,
            l2cache: RefCell::new(Cache::new(l2size)),
        }
    }

    pub fn read_line_without_probe(&self, line: LeU64) -> CacheAccessResult<CacheLine>
    where
        M: CacheFetch,
    {
        self.l2cache
            .borrow_mut()
            .read_line_without_probe(line, &self.shared)
    }
}

impl<M: CacheInvalidate> CacheInvalidate for LocalMemory<M> {
    fn invalidate(&self, line: LeU64) {
        self.l2cache
            .borrow_mut()
            .invalidate_global(line, &self.shared)
    }

    fn invalidate_all(&self) {
        self.l2cache
            .borrow_mut()
            .invalidate_all_global(&self.shared)
    }
}

impl<M: CacheFetch> CacheFetch for LocalMemory<M> {
    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        self.l2cache.borrow_mut().probe_attrs(line, &self.shared)
    }

    fn read_line(&self, line: LeU64) -> CacheAccessResult<CacheLine> {
        self.l2cache.borrow_mut().read_line(line, &self.shared)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        self.shared.park_on_line_unlock(line)
    }
}

impl<M: CacheWrite> CacheWrite for LocalMemory<M> {
    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        self.l2cache
            .borrow_mut()
            .write_line(line, val, &self.shared)
    }

    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        self.l2cache.borrow_mut().lock(line, &self.shared)
    }

    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        self.l2cache.borrow_mut().unlock(line, &self.shared)
    }
}

pub type LocalMemoryBus = LocalMemory<Arc<MemoryBus>>;
