use bytemuck::{AnyBitPattern, NoUninit, Zeroable};
use clever_emu_decode::op::Operand;
use clever_emu_errors::{AccessKind, CPUException, CPUResult, FaultCharacteristics, FaultStatus};
use clever_emu_regs::Regs;
use clever_emu_types::CpuExecutionMode;

use crate::mem::{AddrResolver, DataCache, InstrCache, L2Cache};
use clever_emu_mem::{
    bus::{GlobalMemory, LocalMemory},
    cache::CacheLine,
    io::IoBus,
    phys::Page,
};

use std::{cell::Cell, sync::Arc};

use clever_emu_primitives::primitive::*;

pub struct CpuOperand{
    pub cs: Operand,
    pub imm_val: LeU128,
}

pub struct Cpu {
    regs: Regs,
    l2cache: L2Cache,
    l1dcache: DataCache,
    l1icache: InstrCache,
    addr_resolver: AddrResolver,
    fetch_ip: Cell<LeI64>,
}

#[derive(Copy, Clone)]
pub struct CpuMemorySizes {
    pub l2size: usize,
    pub l1dsize: usize,
    pub l1isize: usize,
    pub l1asize: usize,
    pub tlbsize: usize,

    #[doc(hidden)]
    pub __non_exhaustive: (),
}

impl Default for CpuMemorySizes {
    fn default() -> Self {
        Self {
            l2size: 1024 * 1024,
            l1dsize: 256 * 1024,
            l1isize: 256 * 1024,
            l1asize: 128 * 1024,
            tlbsize: 512,
            __non_exhaustive: (),
        }
    }
}

// Machine ID 018de148-0a63-7e5d-a60f-2a0ff03effe8
pub const CPUID: [LeU64; 2] = [
    LeU64::new(0xa60f2a0ff03effe8),
    LeU64::new(0x018de1480a637e5d),
];

impl Cpu {
    pub fn new(l3cache: Arc<GlobalMemory>, iobus: Arc<IoBus>, memory_sizes: CpuMemorySizes) -> Cpu {
        let l2cache = L2Cache::new(LocalMemory::new(
            l3cache,
            memory_sizes.l2size / (CacheLine::SIZE as usize),
        ));

        let l2cache_data = L2Cache::clone(&l2cache);
        let l2cache_instr = L2Cache::clone(&l2cache);
        let l2cache_addr = L2Cache::clone(&l2cache);

        let l1dsize = memory_sizes.l1dsize / (CacheLine::SIZE as usize);
        let l1isize = memory_sizes.l1isize / (CacheLine::SIZE as usize);
        let l1asize = memory_sizes.l1asize / (CacheLine::SIZE as usize);

        Cpu {
            regs: Regs::new(CPUID),
            l2cache,
            l1dcache: DataCache::new(l1dsize, l2cache_data, iobus),
            l1icache: InstrCache::new(l1isize, l2cache_instr),
            addr_resolver: AddrResolver::new(l1asize, memory_sizes.tlbsize, l2cache_addr),
            fetch_ip: Cell::new(LeI64::new(0xff00)),
        }
    }

    pub fn current_mode(&self) -> CpuExecutionMode {
        self.regs.mode.xm().mode()
    }

    pub fn read<T: AnyBitPattern + NoUninit>(&self, addr: LeI64) -> CPUResult<T> {
        self.read_privileged(addr, self.current_mode())
    }

    pub fn read_privileged<T: AnyBitPattern + NoUninit>(
        &self,
        addr: LeI64,
        xm: CpuExecutionMode,
    ) -> CPUResult<T> {
        let mut val = T::zeroed();
        self.read_bytes_privileged(addr, bytemuck::bytes_of_mut(&mut val), xm)?;
        Ok(val)
    }

    pub fn read_bytes(&self, addr: LeI64, bytes: &mut [u8]) -> CPUResult<()> {
        self.read_bytes_privileged(addr, bytes, self.current_mode())
    }

    /// Reads `bytes` out of memory starting from `addr`, performing virtual address resolution.
    /// Each maximally-sized, adjacent, non-overlapping segment of `bytes` that is at most [`CacheLine::SIZE`] bytes is guaranteed to follow the consistency rules specified in the Clever-ISA Memory Model.
    /// This function takes `xm` as the privilege mode to perform the access as.
    pub fn read_bytes_privileged(
        &self,
        mut addr: LeI64,
        bytes: &mut [u8],
        xm: CpuExecutionMode,
    ) -> CPUResult<()> {
        for chunk in bytes.chunks_mut(CacheLine::SIZE as usize) {
            self.read_line_sized(addr, chunk, xm)?;
            addr += CacheLine::SIZE as i64;
        }

        Ok(())
    }

    fn read_line_sized(
        &self,
        addr: LeI64,
        bytes: &mut [u8],
        xm: CpuExecutionMode,
    ) -> CPUResult<()> {
        if self.regs.cr0.pg() {
            let len = bytes.len() as i64;
            let end_addr = addr + len;

            if (addr & !(Page::SIZE - 1)) == (end_addr & !(Page::SIZE - 1)) {
                let paddr = self
                    .addr_resolver
                    .resolve_vaddr(addr, AccessKind::Access, xm)?;
                self.l1dcache.read(paddr, bytes).map_err(|_| {
                    CPUException::PageFault(
                        addr,
                        FaultCharacteristics {
                            pref: paddr,
                            access_kind: AccessKind::Allocate,
                            status: FaultStatus::with_non_paged(true),
                            ..Zeroable::zeroed()
                        },
                    )
                })
            } else {
                let page_end = end_addr & (!(Page::SIZE - 1));
                let init_len = (page_end - addr).get() as u64;
                let (bytes_left, bytes_right) = bytes.split_at_mut(init_len as usize);
                let init_paddr = self
                    .addr_resolver
                    .resolve_vaddr(addr, AccessKind::Access, xm)?;
                let tail_paddr =
                    self.addr_resolver
                        .resolve_vaddr(page_end, AccessKind::Access, xm)?;

                if tail_paddr == (init_paddr + init_len) {
                    // As an optimization, if two adjacent pages are physically adjacent, fallback to using dual-fetch
                    self.l1dcache.read(init_paddr, bytes).map_err(|_| {
                        CPUException::PageFault(
                            addr,
                            FaultCharacteristics {
                                pref: init_paddr,
                                access_kind: AccessKind::Allocate,
                                status: FaultStatus::with_non_paged(true),
                                ..Zeroable::zeroed()
                            },
                        )
                    })
                } else {
                    let _guard1 = self.l1dcache.lock(init_paddr).map_err(|_| {
                        CPUException::PageFault(
                            addr,
                            FaultCharacteristics {
                                pref: init_paddr,
                                access_kind: AccessKind::Allocate,
                                status: FaultStatus::with_non_paged(true),
                                ..Zeroable::zeroed()
                            },
                        )
                    })?;
                    let _guard2 = self.l1dcache.lock(tail_paddr).map_err(|_| {
                        CPUException::PageFault(
                            addr,
                            FaultCharacteristics {
                                pref: tail_paddr,
                                access_kind: AccessKind::Allocate,
                                status: FaultStatus::with_non_paged(true),
                                ..Zeroable::zeroed()
                            },
                        )
                    })?;
                    self.l1dcache.read(init_paddr, bytes_left).map_err(|_| {
                        CPUException::PageFault(
                            addr,
                            FaultCharacteristics {
                                pref: init_paddr,
                                access_kind: AccessKind::Allocate,
                                status: FaultStatus::with_non_paged(true),
                                ..Zeroable::zeroed()
                            },
                        )
                    })?;
                    self.l1dcache.read(tail_paddr, bytes_right).map_err(|_| {
                        CPUException::PageFault(
                            addr,
                            FaultCharacteristics {
                                pref: tail_paddr,
                                access_kind: AccessKind::Allocate,
                                status: FaultStatus::with_non_paged(true),
                                ..Zeroable::zeroed()
                            },
                        )
                    })
                }
            }
        } else {
            let addr = addr.cast_sign();
            if (64 - addr.leading_zeros() as u64) > 32 + (4 * clever_emu_regs::cpuid::CPUEX2_PAS) {
                return Err(CPUException::PageFault(
                    addr.cast_sign(),
                    FaultCharacteristics {
                        pref: addr,
                        access_kind: AccessKind::Access,
                        status: FaultStatus::with_non_paged(true).insert_non_canonical(true),
                        ..Zeroable::zeroed()
                    },
                ));
            }

            self.l1dcache.read(addr, bytes).map_err(|_| {
                CPUException::PageFault(
                    addr.cast_sign(),
                    FaultCharacteristics {
                        pref: addr,
                        access_kind: AccessKind::Allocate,
                        status: FaultStatus::with_non_paged(true),
                        ..Zeroable::zeroed()
                    },
                )
            })
        }
    }

    pub fn write<T: NoUninit>(&self, addr: LeI64, val: &T) -> CPUResult<()> {
        self.write_privileged(addr, val, self.current_mode())
    }

    pub fn write_privileged<T: NoUninit>(
        &self,
        addr: LeI64,
        val: &T,
        xm: CpuExecutionMode,
    ) -> CPUResult<()> {
        self.write_bytes_privileged(addr, bytemuck::bytes_of(val), xm)
    }

    pub fn write_bytes(&self, addr: LeI64, bytes: &[u8]) -> CPUResult<()> {
        self.write_bytes_privileged(addr, bytes, self.current_mode())
    }

    pub fn write_bytes_privileged(
        &self,
        mut addr: LeI64,
        bytes: &[u8],
        xm: CpuExecutionMode,
    ) -> CPUResult<()> {
        let data_len = bytes.len() as u64 as i64;
        self.addr_resolver
            .resolve_vaddr(addr, AccessKind::Write, xm)?;
        self.addr_resolver
            .resolve_vaddr(addr + data_len, AccessKind::Write, xm)?;

        for chunk in bytes.chunks(CacheLine::SIZE as usize) {
            self.write_line_sized(addr, chunk, xm)?;
            addr += CacheLine::SIZE as i64;
        }
        Ok(())
    }

    fn write_line_sized(&self, addr: LeI64, bytes: &[u8], xm: CpuExecutionMode) -> CPUResult<()> {
        if self.regs.cr0.pg() {
            let data_len = bytes.len() as u64 as i64;
            let end_page = (addr + data_len) & !(Page::SIZE - 1);
            let head_len = (end_page - addr).get();
            let (head, tail) = bytes.split_at(head_len as usize);
            let head_paddr = self
                .addr_resolver
                .resolve_vaddr(addr, AccessKind::Write, xm)?;
            let tail_paddr = self
                .addr_resolver
                .resolve_vaddr(end_page, AccessKind::Write, xm)?;
            let _guard1 = self.l1dcache.lock(head_paddr).map_err(|_| {
                CPUException::PageFault(
                    addr,
                    FaultCharacteristics {
                        pref: head_paddr,
                        access_kind: AccessKind::Allocate,
                        status: FaultStatus::with_non_paged(true),
                        ..Zeroable::zeroed()
                    },
                )
            })?;
            let _guard2 = self.l1dcache.lock(tail_paddr).map_err(|_| {
                CPUException::PageFault(
                    addr,
                    FaultCharacteristics {
                        pref: tail_paddr,
                        access_kind: AccessKind::Allocate,
                        status: FaultStatus::with_non_paged(true),
                        ..Zeroable::zeroed()
                    },
                )
            })?;
            self.l1dcache.write(head_paddr, head).map_err(|_| {
                CPUException::PageFault(
                    addr,
                    FaultCharacteristics {
                        pref: head_paddr,
                        access_kind: AccessKind::Allocate,
                        status: FaultStatus::with_non_paged(true),
                        ..Zeroable::zeroed()
                    },
                )
            })?;
            self.l1dcache.write(tail_paddr, tail).map_err(|_| {
                CPUException::PageFault(
                    addr,
                    FaultCharacteristics {
                        pref: tail_paddr,
                        access_kind: AccessKind::Allocate,
                        status: FaultStatus::with_non_paged(true),
                        ..Zeroable::zeroed()
                    },
                )
            })
        } else {
            let addr = addr.cast_sign();
            if (64 - addr.leading_zeros() as u64) > 32 + (4 * clever_emu_regs::cpuid::CPUEX2_PAS) {
                return Err(CPUException::PageFault(
                    addr.cast_sign(),
                    FaultCharacteristics {
                        pref: addr,
                        access_kind: AccessKind::Write,
                        status: FaultStatus::with_non_paged(true).insert_non_canonical(true),
                        ..Zeroable::zeroed()
                    },
                ));
            }

            self.l1dcache.write(addr, bytes).map_err(|_| {
                CPUException::PageFault(
                    addr.cast_sign(),
                    FaultCharacteristics {
                        pref: addr,
                        access_kind: AccessKind::Allocate,
                        status: FaultStatus::with_non_paged(true),
                        ..Zeroable::zeroed()
                    },
                )
            })
        }
    }

    fn fetch_iword(&self) -> CPUResult<BeU16> {
        let next_iword_addr = self.fetch_ip.get() + 2;
        self.fetch_ip.set(next_iword_addr);
        let iword = self.l1icache.fetch().map_err(|_| {
            CPUException::PageFault(
                next_iword_addr - 2,
                FaultCharacteristics {
                    pref: self.l1icache.cur_ip() - 2,
                    access_kind: AccessKind::Allocate,
                    status: FaultStatus::with_non_paged(true),
                    ..Zeroable::zeroed()
                },
            )
        })?;
        if self.regs.cr0.pg() {
            if (next_iword_addr & (Page::SIZE - 1)) == 0 {
                let new_paddr = self.addr_resolver.resolve_vaddr(
                    next_iword_addr,
                    AccessKind::Execute,
                    self.current_mode(),
                )?;
                self.l1icache
                    .reposition_after_page_boundary(new_paddr)
                    .map_err(|_| {
                        CPUException::PageFault(
                            next_iword_addr,
                            FaultCharacteristics {
                                pref: new_paddr,
                                access_kind: AccessKind::Allocate,
                                status: FaultStatus::with_non_paged(true),
                                ..Zeroable::zeroed()
                            },
                        )
                    })?;
            }
        }
        Ok(iword)
    }
}
