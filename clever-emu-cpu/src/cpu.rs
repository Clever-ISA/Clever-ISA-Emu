use bytemuck::{AnyBitPattern, NoUninit, Zeroable};
use clever_emu_decode::{
    decode::{FromInstructionStream, InstructionStream},
    instr::{Instruction, Operand},
};
use clever_emu_errors::{AccessKind, CPUException, CPUResult, FaultCharacteristics, FaultStatus};
use clever_emu_regs::{Flags, Regs};
use clever_emu_types::{
    CleverRegister, CpuExecutionMode, Extension, ShiftSizeControl, SizeControl,
};

use crate::mem::{AddrResolver, DataCache, DataCacheLockGuard, InstrCache, L2Cache};
use clever_emu_mem::{
    bus::{GlobalMemory, LocalMemory, LocalMemoryLockGuard},
    cache::CacheLine,
    io::IoBus,
    phys::Page,
};

use core::borrow::Borrow;
use std::{cell::Cell, sync::Arc};

use clever_emu_primitives::primitive::*;

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

fn logical_flags(res_val: LeU64, ss: SizeControl) -> Flags {
    let mut flags = Flags::empty();

    flags.set_zero(res_val == LeU64::new(0));

    flags.set_negative((res_val & 1u64 << (ss.as_bits() - 1)) == 1);

    flags.set_parity((res_val.count_ones() & 1) != 0);

    flags
}

pub fn compute_logical<F: Fn(LeU64, LeU64) -> LeU64>(
    f: F,
    val1: LeU64,
    val2: LeU64,
    ss: SizeControl,
) -> (LeU64, Flags) {
    let res_val = f(val1, val2) & ss.as_regwidth_mask();

    (res_val, logical_flags(res_val, ss))
}

pub fn compute_arithmetic<F: Fn(LeU64, LeU64) -> (LeU64, bool)>(
    f: F,
    val1: LeU64,
    val2: LeU64,
    ss: SizeControl,
) -> (LeU64, Flags) {
    let (res_val, full_carry) = f(val1, val2);

    let carry =
        (full_carry & (ss == SizeControl::Double)) | ((res_val & ss.as_rangeless_shift_1()) != 0);

    let sign_bit = LeU64::new(1) << (ss.as_bits() - 1);
    let overflow = ((val1 ^ val2 ^ res_val) & sign_bit).get() != carry as u64;

    let res = res_val & ss.as_regwidth_mask();

    let flags = logical_flags(res, ss)
        .insert_carry(carry)
        .insert_overflow(overflow);

    (res, flags)
}

pub struct Stream<'a>(&'a Cpu);

impl<'a> InstructionStream for Stream<'a> {
    fn next_iword(&mut self) -> CPUResult<BeU16> {
        self.0.fetch_iword()
    }
}

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

    pub fn as_instruction_stream(&self) -> Stream {
        Stream(self)
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

    fn is_simple(opr: &Operand) -> bool {
        match opr {
            Operand::Register(reg) => reg.reg().get() < 16,
            Operand::SmallImm(_) => true,
            Operand::LargeImm(cs, _) => !cs.mem(),
            _ => false,
        }
    }

    pub fn check_simple<I: IntoIterator>(&self, it: I) -> CPUResult<()>
    where
        I::Item: Borrow<Operand>,
    {
        if it
            .into_iter()
            .filter(|op| Self::is_simple(op.borrow()))
            .count()
            < 1
        {
            Ok(())
        } else {
            Err(CPUException::Undefined)
        }
    }

    pub fn check_wf(&self, op: &Operand) -> CPUResult<()> {
        match op {
            Operand::Register(reg) => {
                self.regs.validate_wf(reg.reg())?;
                #[cfg(feature = "vector")]
                {
                    if reg.vec() {
                        self.regs.cr0.check_extension(Extension::Vector)?;

                        if (reg.reg().0 & 1) != 0 || !matches!(reg.reg(), CleverRegister(64..=127))
                        {
                            Err(CPUException::Undefined)
                        } else {
                            Ok(())
                        }
                    } else if reg.ss() == SizeControl::Quad {
                        Err(CPUException::Undefined)
                    } else {
                        Ok(())
                    }
                }
                #[cfg(not(feature = "vector"))]
                {
                    if reg.ss() == SizeControl::Quad {
                        Err(CPUException::Undefined)
                    } else {
                        Ok(())
                    }
                }
            }
            Operand::Indirect(indr) => {
                if indr.ss() == SizeControl::Quad {
                    self.regs.cr0.check_extension(Extension::Vector)
                } else {
                    Ok(())
                }
            }
            Operand::LargeImm(cs, _) => {
                if !cs.disp() && cs.index() != CleverRegister(0) {
                    Err(CPUException::Undefined)
                } else if (cs.mem() || cs.rel()) && cs.ss() == ShiftSizeControl::Quad {
                    Err(CPUException::Undefined)
                } else if !cs.mem() && cs.zz() != SizeControl::Byte {
                    Err(CPUException::Undefined)
                } else if cs.ss() == ShiftSizeControl::Quad || cs.zz() == SizeControl::Quad {
                    self.regs.cr0.check_extension(Extension::Vector)
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }

    pub fn check_scalar(&self, op: &Operand) -> CPUResult<()> {
        match op {
            Operand::Register(reg) => {
                #[cfg(feature = "vector")]
                {
                    if reg.vec() {
                        Err(CPUException::Undefined)
                    } else {
                        Ok(())
                    }
                }
                #[cfg(not(feature = "vector"))]
                {
                    Ok(())
                }
            }
            Operand::LargeImm(cs, _) => {
                if cs.ss() == ShiftSizeControl::Quad || cs.zz() == SizeControl::Quad {
                    Err(CPUException::Undefined)
                } else {
                    Ok(())
                }
            }
            Operand::Indirect(indr) => {
                if indr.ss() == SizeControl::Quad {
                    Err(CPUException::Undefined)
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }

    pub fn check_scalar_or_vreg(&self, op: &Operand) -> CPUResult<()> {
        match op {
            Operand::LargeImm(cs, _) => {
                if cs.ss() == ShiftSizeControl::Quad || cs.zz() == SizeControl::Quad {
                    Err(CPUException::Undefined)
                } else {
                    Ok(())
                }
            }
            Operand::Indirect(indr) => {
                if indr.ss() == SizeControl::Quad {
                    Err(CPUException::Undefined)
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }

    pub fn check_int(&self, op: &Operand) -> CPUResult<()> {
        match op {
            Operand::Register(reg) => match reg.reg() {
                CleverRegister(0..=15) | CleverRegister(64..=127) => Ok(()),
                _ => Err(CPUException::Undefined),
            },
            _ => Ok(()),
        }
    }

    pub fn check_writable(&self, op: &Operand) -> CPUResult<()> {
        match op {
            Operand::Register(_) | Operand::Indirect(_) => Ok(()),
            Operand::LargeImm(cs, _) if cs.mem() => Ok(()),
            _ => Err(CPUException::Undefined),
        }
    }

    pub fn validate_write(&self, op: &Operand, val: LeU64) -> CPUResult<()> {
        let size = self.op_size(op);
        let val = val & size.as_regwidth_mask();
        match op {
            Operand::Register(reg) => {
                self.regs
                    .validate_before_writing(reg.reg(), val, self.current_mode())
            }
            Operand::Indirect(_) | Operand::LargeImm(_, _) => {
                let addr = self.compute_addr(op).ok_or(CPUException::Undefined)??;

                let end_addr = addr + size.as_bytes() as i64;

                self.addr_resolver
                    .resolve_vaddr(addr, AccessKind::Write, self.current_mode())?;
                self.addr_resolver.resolve_vaddr(
                    end_addr,
                    AccessKind::Write,
                    self.current_mode(),
                )?;

                Ok(())
            }
            _ => Err(CPUException::Undefined),
        }
    }

    pub fn op_size(&self, op: &Operand) -> SizeControl {
        match op {
            Operand::Register(reg) => reg.ss(),
            Operand::Indirect(indr) => indr.ss(),
            Operand::SmallImm(imm) => {
                if imm.rel() {
                    SizeControl::Double
                } else {
                    SizeControl::Half
                }
            }
            Operand::LargeImm(cs, _) => {
                if cs.mem() {
                    cs.zz()
                } else if cs.rel() {
                    SizeControl::Double
                } else {
                    cs.ss().as_size_control()
                }
            }
        }
    }

    pub fn read_op(&self, op: &Operand) -> CPUResult<LeU64> {
        let size = self.op_size(op);

        if size == SizeControl::Quad {
            return Err(CPUException::Undefined);
        }

        if let Some(addr) = self.compute_addr(op) {
            let addr = addr?;

            let mut bytes = LeU64::new(0);

            self.read_bytes(
                addr,
                &mut bytemuck::bytes_of_mut(&mut bytes)[..size.as_bytes()],
            )?;

            Ok(bytes)
        } else {
            match op {
                Operand::Register(reg) => {
                    self.regs
                        .validate_before_reading(reg.reg(), self.current_mode())?;

                    Ok(self.regs[reg.reg()] & size.as_regwidth_mask())
                }
                Operand::SmallImm(imm) => {
                    let val = imm.imm().unsigned_as::<LeU64>();
                    if imm.rel() {
                        let val = val.cast_sign();

                        let val = (val << 52) >> 52;

                        Ok(val.wrapping_add(self.regs.ip).cast_sign())
                    } else {
                        Ok(val)
                    }
                }
                Operand::LargeImm(cs, wide) => {
                    let val = wide.0.unsigned_as::<LeU64>();

                    if cs.rel() {
                        let val = val.cast_sign();

                        Ok(cs
                            .ss()
                            .sign_extend(val)
                            .wrapping_add(self.regs.ip)
                            .cast_sign())
                    } else {
                        Ok(val & cs.ss().as_regwidth_mask())
                    }
                }
                Operand::Indirect(_) => unreachable!("indirect should have an address"),
            }
        }
    }

    pub fn write_op(&mut self, op: &Operand, val: LeU64) -> CPUResult<()> {
        let size = self.op_size(op);

        if size == SizeControl::Quad {
            return Err(CPUException::Undefined);
        }

        if let Some(addr) = self.compute_addr(op) {
            let addr = addr?;

            self.write_bytes(addr, &bytemuck::bytes_of(&val)[..size.as_bytes()])?;

            Ok(())
        } else {
            if let Operand::Register(reg) = op {
                self.regs
                    .validate_before_writing(reg.reg(), val, self.current_mode())?;
                self.regs[reg.reg()] = val & size.as_regwidth_mask();
                Ok(())
            } else {
                Err(CPUException::Undefined)
            }
        }
    }

    pub fn perform_rmw(
        &mut self,
        dest: &Operand,
        mut op: impl FnMut(LeU64, &Cpu) -> CPUResult<LeU64>,
        under_lock: bool,
    ) -> CPUResult<()> {
        let op_size = self.op_size(dest);
        let _guard = if under_lock {
            if let Some(vaddr) = self.compute_addr(dest) {
                let vaddr = vaddr?;
                let end_vaddr = vaddr + (op_size.as_bytes() as i64 - 1);

                let start_paddr = self.addr_resolver.resolve_vaddr(
                    vaddr,
                    AccessKind::Access,
                    self.current_mode(),
                )?;
                let end_paddr = self.addr_resolver.resolve_vaddr(
                    end_vaddr,
                    AccessKind::Access,
                    self.current_mode(),
                )?;

                if (start_paddr & !(CacheLine::SIZE - 1)) != (end_paddr & !(CacheLine::SIZE - 1)) {
                    Some((
                        self.l1dcache.lock(start_paddr).map_err(|_| {
                            CPUException::PageFault(
                                vaddr,
                                FaultCharacteristics {
                                    pref: start_paddr,
                                    access_kind: AccessKind::Allocate,
                                    status: FaultStatus::with_non_paged(true),
                                    ..Zeroable::zeroed()
                                },
                            )
                        })?,
                        Some(self.l1dcache.lock(end_paddr).map_err(|_| {
                            CPUException::PageFault(
                                vaddr,
                                FaultCharacteristics {
                                    pref: end_paddr,
                                    access_kind: AccessKind::Allocate,
                                    status: FaultStatus::with_non_paged(true),
                                    ..Zeroable::zeroed()
                                },
                            )
                        })?),
                    ))
                } else {
                    Some((
                        self.l1dcache.lock(start_paddr).map_err(|_| {
                            CPUException::PageFault(
                                vaddr,
                                FaultCharacteristics {
                                    pref: start_paddr,
                                    access_kind: AccessKind::Allocate,
                                    status: FaultStatus::with_non_paged(true),
                                    ..Zeroable::zeroed()
                                },
                            )
                        })?,
                        None,
                    ))
                }
            } else {
                None
            }
        } else {
            None
        };

        let val = self.read_op(dest)?;

        let res = op(val, self)?;

        if let Some(addr) = self.compute_addr(dest) {
            let addr = addr?;

            self.write_bytes(addr, &bytemuck::bytes_of(&val)[..op_size.as_bytes()])?;
            Ok(())
        } else {
            if let Operand::Register(reg) = dest {
                self.regs[reg.reg()] = val & op_size.as_regwidth_mask();
                Ok(())
            } else {
                return Err(CPUException::Undefined);
            }
        }
    }

    fn compute_addr(&self, op: &Operand) -> Option<CPUResult<LeI64>> {
        match op {
            Operand::Indirect(indr) => {
                let base = indr.base();
                let index = indr.index();
                let scale = indr.scale();

                let base_val = self.regs[base].cast_sign();
                let index_val = self.regs[index].cast_sign();
                let scale = LeI64::new(1) << (scale.get() as u32);

                Some(Ok(index_val.wrapping_mul(scale).wrapping_add(base_val)))
            }
            Operand::LargeImm(cs, val) => {
                let mut val = val.0.unsigned_as::<LeI64>();

                if cs.mem() {
                    if cs.disp() {
                        val += self.regs[cs.index()].cast_sign();
                    }

                    if cs.rel() {
                        val = cs.ss().sign_extend(val).wrapping_add(self.regs.ip);
                    }

                    if cs.ss() == ShiftSizeControl::Quad {
                        Some(Err(CPUException::Undefined))
                    } else {
                        Some(Ok(val))
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn tick(&mut self) -> CPUResult<()> {
        match self.as_instruction_stream().fetch::<Instruction>()? {
            Instruction::Und(_) | Instruction::UndFFF(_) => Err(CPUException::Undefined),
            Instruction::Add(h, dest, src) => {
                self.check_wf(&dest)?;
                self.check_wf(&src)?;
                self.check_writable(&dest)?;
                self.check_int(&dest)?;
                self.check_int(&src)?;
                self.check_simple([&dest, &src])?;

                let mut flags = Flags::empty();

                self.perform_rmw(
                    &dest,
                    |src1, cpu| {
                        let intermediate_size = cpu.op_size(&dest).max(cpu.op_size(&src));
                        let src2 = cpu.read_op(&src)?;

                        let res;
                        (res, flags) = compute_arithmetic(
                            LeU64::overflowing_add,
                            src1,
                            src2,
                            intermediate_size,
                        );

                        Ok(res)
                    },
                    h.lock(),
                )?;

                if !h.supress_flags() {
                    self.regs.flags = flags;
                }
                Ok(())
            }
            Instruction::Sub(h, dest, src) => {
                self.check_wf(&dest)?;
                self.check_wf(&src)?;
                self.check_writable(&dest)?;
                self.check_int(&dest)?;
                self.check_int(&src)?;
                self.check_simple([&dest, &src])?;

                let mut flags = Flags::empty();

                self.perform_rmw(
                    &dest,
                    |src1, cpu| {
                        let intermediate_size = cpu.op_size(&dest).max(cpu.op_size(&src));
                        let src2 = (!cpu.read_op(&src)?).wrapping_add(LeU64::new(1));

                        let res;
                        (res, flags) = compute_arithmetic(
                            LeU64::overflowing_add,
                            src1,
                            src2,
                            intermediate_size,
                        );

                        Ok(res)
                    },
                    h.lock(),
                )?;

                if !h.supress_flags() {
                    self.regs.flags = flags;
                }
                Ok(())
            }
            Instruction::And(h, dest, src) => {
                self.check_wf(&dest)?;
                self.check_wf(&src)?;
                self.check_writable(&dest)?;
                self.check_int(&dest)?;
                self.check_int(&src)?;
                self.check_simple([&dest, &src])?;

                let mut flags = Flags::empty();

                self.perform_rmw(
                    &dest,
                    |src1, cpu| {
                        let intermediate_size = cpu.op_size(&dest).max(cpu.op_size(&src));
                        let src2 = (!cpu.read_op(&src)?).wrapping_add(LeU64::new(1));

                        let res = src1 & src2;

                        flags = logical_flags(res, intermediate_size);

                        Ok(res)
                    },
                    h.lock(),
                )?;

                if !h.supress_flags() {
                    self.regs.flags.set_logical(flags);
                }
                Ok(())
            }
            Instruction::Or(h, dest, src) => {
                self.check_wf(&dest)?;
                self.check_wf(&src)?;
                self.check_writable(&dest)?;
                self.check_int(&dest)?;
                self.check_int(&src)?;
                self.check_simple([&dest, &src])?;

                let mut flags = Flags::empty();

                self.perform_rmw(
                    &dest,
                    |src1, cpu| {
                        let intermediate_size = cpu.op_size(&dest).max(cpu.op_size(&src));
                        let src2 = (!cpu.read_op(&src)?).wrapping_add(LeU64::new(1));

                        let res = src1 | src2;

                        flags = logical_flags(res, intermediate_size);

                        Ok(res)
                    },
                    h.lock(),
                )?;

                if !h.supress_flags() {
                    self.regs.flags.set_logical(flags);
                }
                Ok(())
            }
            Instruction::Xor(h, dest, src) => {
                self.check_wf(&dest)?;
                self.check_wf(&src)?;
                self.check_writable(&dest)?;
                self.check_int(&dest)?;
                self.check_int(&src)?;
                self.check_simple([&dest, &src])?;

                let mut flags = Flags::empty();

                self.perform_rmw(
                    &dest,
                    |src1, cpu| {
                        let intermediate_size = cpu.op_size(&dest).max(cpu.op_size(&src));
                        let src2 = (!cpu.read_op(&src)?).wrapping_add(LeU64::new(1));

                        let res = src1 ^ src2;

                        flags = logical_flags(res, intermediate_size);

                        Ok(res)
                    },
                    h.lock(),
                )?;

                if !h.supress_flags() {
                    self.regs.flags.set_logical(flags);
                }
                Ok(())
            }
            Instruction::Mul(h) => {
                let val1 = self.regs.gprs[0] & h.size().as_regwidth_mask();
                let val2 = self.regs.gprs[3] & h.size().as_regwidth_mask();

                let (lo, hi) = val1.widening_mul(val2);

                let real_hi = (hi.rangeless_shl(64 - h.size().as_bits())
                    | lo.rangeless_shr(h.size().as_bits()))
                    & h.size().as_regwidth_mask();

                self.regs.gprs[0] = lo & h.size().as_regwidth_mask();
                self.regs.gprs[3] = real_hi;

                Ok(())
            }
            _ => Err(CPUException::Undefined),
        }
    }
}
