use bytemuck::Zeroable;
use clever_emu_errors::{AccessKind, CPUException, CPUResult, FaultCharacteristics, FaultStatus};
use clever_emu_mem::{
    bus::{LocalMemory, LocalMemoryBus, LocalMemoryLockGuard},
    cache::{CacheAccessError, CacheInvalidate, CacheLine, CacheWrite},
    io::IoBus,
    phys::Page,
};
use clever_emu_regs::{cpuid, PgTab};
use clever_emu_types::{CpuExecutionMode, ExecutionMode};
use core::cell::UnsafeCell;
use lru_time_cache::LruCache;
use std::sync::Arc;
use std::{cell::RefCell, rc::Rc};

use clever_emu_primitives::{const_transmute_safe, primitive::*};

use crate::page::{LpePermission, PageEntry};

pub type L2Cache = Rc<LocalMemory>;

pub type L1Cache = LocalMemoryBus<L2Cache>;

/// ## Notes
/// Err will never be `Locked`
pub type MemoryResult<T = ()> = Result<T, CacheAccessError>;

#[repr(u64)]
enum PadZero {
    Zero = 0,
}

pub struct DataCache {
    cache: L1Cache,
    line_buffer: UnsafeCell<Option<(LeU64, PadZero, [CacheLine; 2])>>,
    iobus: Arc<IoBus>,
}

impl DataCache {
    pub fn new(l1size: usize, l2cache: L2Cache, iobus: Arc<IoBus>) -> Self {
        Self {
            cache: L1Cache::new(l2cache, l1size),
            line_buffer: UnsafeCell::new(None),
            iobus,
        }
    }

    fn read_lines(&self, line_addr: LeU64) -> MemoryResult<[CacheLine; 2]> {
        let line_buffer = unsafe { &mut *self.line_buffer.get() };
        if let Some((addr, _, lines)) = &line_buffer {
            if *addr == line_addr {
                return Ok(*lines);
            } else {
                let _guard1 = self.cache.lock_blocking(line_addr)?;
                let _guard2 = self.cache.lock_blocking(line_addr + CacheLine::SIZE)?;
                self.cache.write_line(line_addr, lines[0])?;
                self.cache
                    .write_line(line_addr + CacheLine::SIZE, lines[1])?;
            }
        }

        let (lines, _) = self.cache.read_dual_blocking(line_addr)?;

        *line_buffer = Some((line_addr, PadZero::Zero, lines));

        Ok(lines)
    }

    fn write_lines(&self, line_addr: LeU64, lines: [CacheLine; 2]) -> MemoryResult {
        let line_buffer = unsafe { &mut *self.line_buffer.get() };
        if let Some((addr, _, buffered_lines)) = line_buffer {
            if *addr == line_addr {
                *buffered_lines = lines;
            } else {
                let _guard1 = self.cache.lock_blocking(line_addr)?;
                let _guard2 = self.cache.lock_blocking(line_addr + CacheLine::SIZE)?;
                self.cache.write_line(line_addr, buffered_lines[0])?;
                self.cache
                    .write_line(line_addr + CacheLine::SIZE, buffered_lines[1])?;
            }
        }
        *line_buffer = Some((line_addr, PadZero::Zero, lines));

        Ok(())
    }

    pub fn flush_line(&self, paddr: LeU64, num_bytes: usize) -> MemoryResult {
        let line_addr = paddr & !(CacheLine::SIZE - 1);

        let line_buffer = unsafe { &mut *self.line_buffer.get() };

        if let Some((addr, _, buffered_lines)) = &line_buffer {
            if *addr == line_addr || (*addr) + 1 == line_addr {
                let _guard1 = self.cache.lock_blocking(line_addr)?;
                let _guard2 = self.cache.lock_blocking(line_addr + CacheLine::SIZE)?;
                self.cache.write_line(line_addr, buffered_lines[0])?;
                self.cache
                    .write_line(line_addr + CacheLine::SIZE, buffered_lines[1])?;

                *line_buffer = None;
            }
        }

        self.cache.invalidate(line_addr);

        if ((paddr + (num_bytes as u64)) & !(CacheLine::SIZE - 1)) != line_addr {
            self.cache.invalidate(line_addr + CacheLine::SIZE);
        }
        Ok(())
    }

    pub fn flush_all(&self) -> MemoryResult {
        let line_buffer = unsafe { &mut *self.line_buffer.get() };
        if let Some((addr, _, lines)) = &line_buffer {
            let _guard1 = self.cache.lock_blocking(*addr)?;
            let _guard2 = self.cache.lock_blocking(*addr + CacheLine::SIZE)?;
            self.cache.write_line(*addr, lines[0])?;
            self.cache.write_line(*addr + CacheLine::SIZE, lines[1])?;
        }
        *line_buffer = None;

        self.cache.invalidate_all();
        Ok(())
    }

    /// Allows reading data that occupies at most 2 cache lines total, on the same page
    pub fn read(&self, paddr: LeU64, data: &mut [u8]) -> MemoryResult {
        match self.iobus.read(paddr, data) {
            Ok(()) => Ok(()),
            Err(CacheAccessError::NotPresent) => {
                let offset = (paddr & (CacheLine::SIZE - 1)).get() as usize;
                let lines = self.read_lines(paddr & !(CacheLine::SIZE - 1))?;

                let bytes = bytemuck::bytes_of(&lines);

                let range = &bytes[offset..][..data.len()];
                data.copy_from_slice(range);
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    /// Allows writing data that occupies at most 2 cache lines total, on the same page
    pub fn write(&self, paddr: LeU64, data: &[u8]) -> MemoryResult {
        match self.iobus.write(paddr, data) {
            Ok(()) => Ok(()),
            Err(CacheAccessError::NotPresent) => {
                let offset = (paddr & (CacheLine::SIZE - 1)).get() as usize;

                let mut lines =
                    if offset == 0 && (data.len() & (core::mem::size_of::<CacheLine>() - 1)) == 0 {
                        Zeroable::zeroed()
                    } else {
                        self.read_lines(paddr & !(CacheLine::SIZE - 1))?
                    };

                let bytes = bytemuck::bytes_of_mut(&mut lines);

                let range = &mut bytes[offset..][..data.len()];

                range.copy_from_slice(data);

                self.write_lines(paddr & !(CacheLine::SIZE - 1), lines)
            }
            Err(e) => Err(e),
        }
    }

    /// Locks the cache line that `paddr` belongs to.
    /// For convience, this can take an unaligned `paddr`, and the function will align it downwards to the same cache line
    pub fn lock(&self, paddr: LeU64) -> MemoryResult<LocalMemoryLockGuard<L2Cache>> {
        self.cache
            .lock_blocking(paddr & !(CacheLine::SIZE - 1))
            .map(|(a, _)| a)
    }
}

#[derive(Zeroable)]
struct FetchBuffer {
    line: [BeU16; core::mem::size_of::<CacheLine>() / 2],
    cur_line: LeU64,
    offset: usize,
}

pub struct InstrCache {
    cache: L1Cache,
    fetch_buffer: UnsafeCell<FetchBuffer>,
}

impl InstrCache {
    pub fn new(l1isize: usize, l2cache: L2Cache) -> Self {
        Self {
            cache: L1Cache::new(l2cache, l1isize),
            fetch_buffer: UnsafeCell::new(FetchBuffer::zeroed()),
        }
    }

    pub fn cur_ip(&self) -> LeU64 {
        let fetch_buffer = unsafe { &*self.fetch_buffer.get() };
        fetch_buffer.cur_line | (fetch_buffer.offset << 1) as u64
    }

    pub fn reposition_after_mode_switch(&self, new_ip: LeU64) -> MemoryResult {
        self.cache.invalidate_all_local();

        let fetch_buffer = unsafe { &mut *self.fetch_buffer.get() };
        let offset = (new_ip & (CacheLine::SIZE - 1)).get() as usize;
        let line = new_ip & !(CacheLine::SIZE - 1);

        fetch_buffer.offset = offset >> 1;
        fetch_buffer.cur_line = line;

        let (line, _) = self.cache.read_blocking(line)?;

        fetch_buffer.line = const_transmute_safe(line);

        Ok(())
    }

    pub fn reposition_after_jump(&self, new_ip: LeU64) -> MemoryResult {
        let fetch_buffer = unsafe { &mut *self.fetch_buffer.get() };
        let offset = (new_ip & (CacheLine::SIZE - 1)).get() as usize;
        let line = new_ip & !(CacheLine::SIZE - 1);

        fetch_buffer.offset = offset >> 1;

        if line != fetch_buffer.cur_line {
            fetch_buffer.line = const_transmute_safe(self.cache.read_weak_blocking(line)?.0);
            fetch_buffer.cur_line = line;
        }

        Ok(())
    }

    pub fn reposition_after_page_boundary(&self, next_page: LeU64) -> MemoryResult {
        let fetch_buffer = unsafe { &mut *self.fetch_buffer.get() };

        if next_page != fetch_buffer.cur_line {
            fetch_buffer.line = const_transmute_safe(self.cache.read_weak_blocking(next_page)?.0);
            fetch_buffer.cur_line = next_page;
        }
        Ok(())
    }

    pub fn fetch(&self) -> MemoryResult<BeU16> {
        let fetch_buffer = unsafe { &mut *self.fetch_buffer.get() };

        let word = fetch_buffer.line[fetch_buffer.offset];
        fetch_buffer.offset += 1;
        if fetch_buffer.offset == core::mem::size_of::<CacheLine>() >> 1 {
            fetch_buffer.offset = 0;
            fetch_buffer.cur_line += 1;
            fetch_buffer.line =
                const_transmute_safe(self.cache.read_weak_blocking(fetch_buffer.cur_line)?.0);
        }
        Ok(word)
    }
}

pub struct AddrResolver {
    l1a_cache: L1Cache,
    tlb: RefCell<LruCache<LeI64, (PageEntry, CpuExecutionMode)>>,
    cr3: PgTab,
}

impl AddrResolver {
    pub fn new(l1asize: usize, tlb_size: usize, l2cache: L2Cache) -> Self {
        Self {
            l1a_cache: L1Cache::new(l2cache, l1asize),
            tlb: RefCell::new(LruCache::with_capacity(tlb_size)),
            cr3: PgTab::from_bits(LeU64::new(0)),
        }
    }

    pub fn set_cr3(&mut self, new_cr3: PgTab) {
        self.tlb.get_mut().clear();
        self.cr3 = new_cr3;
    }

    pub fn resolve_vaddr(
        &self,
        vaddr: LeI64,
        access: AccessKind,
        xm: CpuExecutionMode,
    ) -> CPUResult<LeU64> {
        let vpage = vaddr & !(Page::SIZE - 1);
        let addr_offset = (vaddr & (Page::SIZE - 1)).cast_sign();
        let mut cache = self.tlb.borrow_mut();

        let ppage = if let Some(&(paddr, required_rights)) = cache.get(&vaddr) {
            xm.check_mode(required_rights).map_err(|_| {
                CPUException::PageFault(
                    vaddr,
                    clever_emu_errors::FaultCharacteristics {
                        pref: paddr.bits(),
                        flevel: LeU8::new(0),
                        access_kind: access,
                        status: FaultStatus::with_mode(xm.into_xm()),
                        ..Zeroable::zeroed()
                    },
                )
            })?;
            if access == AccessKind::Execute && required_rights != xm {
                return Err(CPUException::PageFault(
                    vaddr,
                    clever_emu_errors::FaultCharacteristics {
                        pref: paddr.bits(),
                        flevel: LeU8::new(0),
                        access_kind: access,
                        status: FaultStatus::with_mode(xm.into_xm()).insert_prevented(true),
                        ..Zeroable::zeroed()
                    },
                ));
            }
            paddr
        } else {
            let width = 64 - (vaddr.leading_ones() + vaddr.leading_zeros());

            let addr_width = 8 * (self.cr3.ptl().get() as u32) + 32;

            if width > addr_width {
                return Err(CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        access_kind: access,
                        status: FaultStatus::with_non_canonical(true),
                        ..Zeroable::zeroed()
                    },
                ));
            }

            let masked_page = vpage.cast_sign() & (!0 >> (64 - addr_width));

            let mut level = match self.cr3.ptl().get() {
                0 => 2,
                1 | 2 => 3,
                3 => 4,
                4 => 5,
                _ => panic!("We validated cr3 a long time ago ptl is at most 4"),
            };

            let mut page_num = (masked_page >> 12) << (64 - 9 * (level as u32 + 1)); // 12 bits is the page size
            let mut cur_tab_addr = self.cr3.addr();
            let mut required_rights = CpuExecutionMode::User;
            let entry = loop {
                let tab_addr_width = 64 - cur_tab_addr.leading_zeros();
                let paddr_width = 32 + 4 * (cpuid::CPUEX2_PAS as u32);
                if tab_addr_width > paddr_width {
                    return Err(CPUException::PageFault(
                        cur_tab_addr.cast_sign(),
                        FaultCharacteristics {
                            pref: cur_tab_addr,
                            access_kind: access,
                            status: FaultStatus::with_non_canonical(true).insert_non_paged(true),
                            ..Zeroable::zeroed()
                        },
                    ));
                }

                let level_page_num = page_num >> 55;
                page_num <<= 9;

                let tab_offset = level_page_num << 3;

                let line = cur_tab_addr | (tab_offset & !(CacheLine::SIZE - 1));

                let line_offset = tab_offset & (CacheLine::SIZE - 1);

                let (line, _) = self.l1a_cache.read_weak_blocking(line).map_err(|_| {
                    CPUException::PageFault(
                        (line | line_offset).cast_sign(),
                        FaultCharacteristics {
                            pref: cur_tab_addr,
                            access_kind: AccessKind::Allocate,
                            status: FaultStatus::with_non_paged(true),
                            ..Zeroable::zeroed()
                        },
                    )
                })?;

                let entry: PageEntry = *bytemuck::from_bytes(
                    &bytemuck::bytes_of(&line)[line_offset.get() as usize..][..8],
                );

                if !entry.validate() {
                    return Err(CPUException::PageFault(
                        vaddr,
                        FaultCharacteristics {
                            pref: cur_tab_addr,
                            access_kind: access,
                            flevel: LeU8::new(level),
                            status: FaultStatus::with_validation_error(true)
                                .insert_nested(true)
                                .insert_mode(xm.into_xm()),
                            ..Zeroable::zeroed()
                        },
                    ));
                } else if entry.perm() == 0 {
                    return Err(CPUException::PageFault(
                        vaddr,
                        FaultCharacteristics {
                            pref: cur_tab_addr,
                            access_kind: access,
                            flevel: LeU8::new(level),
                            status: FaultStatus::with_nested(true).insert_mode(xm.into_xm()),
                            ..Zeroable::zeroed()
                        },
                    ));
                }

                xm.check_mode(entry.xm().mode()).map_err(|_| {
                    CPUException::PageFault(
                        vaddr,
                        FaultCharacteristics {
                            pref: cur_tab_addr,
                            access_kind: access,
                            flevel: LeU8::new(level),
                            status: FaultStatus::with_validation_error(true)
                                .insert_nested(true)
                                .insert_mode(xm.into_xm()),
                            ..Zeroable::zeroed()
                        },
                    )
                })?;

                if required_rights > entry.xm().mode() {
                    required_rights = entry.xm().mode();
                }

                if level == 0 {
                    break entry;
                } else {
                    level -= 1;
                    if !entry.npe_perm().validate() {
                        return Err(CPUException::PageFault(
                            vaddr,
                            FaultCharacteristics {
                                pref: cur_tab_addr,
                                access_kind: access,
                                flevel: LeU8::new(level),
                                status: FaultStatus::with_validation_error(true)
                                    .insert_nested(true)
                                    .insert_mode(xm.into_xm()),
                                ..Zeroable::zeroed()
                            },
                        ));
                    }
                    cur_tab_addr = entry.addr();
                }
            };

            if access == AccessKind::Execute && required_rights != xm {
                return Err(CPUException::PageFault(
                    vaddr,
                    clever_emu_errors::FaultCharacteristics {
                        pref: entry.bits(),
                        flevel: LeU8::new(0),
                        access_kind: access,
                        status: FaultStatus::with_mode(xm.into_xm()).insert_prevented(true),
                        ..Zeroable::zeroed()
                    },
                ));
            }

            cache.insert(vaddr, (entry, required_rights));

            entry
        };
        let perm = ppage.lpe_perm();
        match (access, perm) {
            (AccessKind::Access, _)
            | (AccessKind::Write, LpePermission::Write)
            | (AccessKind::Execute, LpePermission::Exec) => {}
            _ => {
                return Err(CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        pref: ppage.bits(),
                        access_kind: access,
                        flevel: LeU8::new(0),
                        status: FaultStatus::with_mode(xm.into_xm()),
                        ..Zeroable::zeroed()
                    },
                ))
            }
        }

        let page_base = ppage.addr();

        Ok(page_base + addr_offset)
    }
}
