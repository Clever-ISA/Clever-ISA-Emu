use std::{cell::RefCell, collections::VecDeque, convert::TryInto, sync::Arc};

use arch_ops::{
    clever::{
        CleverExtension, CleverImmediate, CleverIndex, CleverInstruction, CleverOpcode,
        CleverOperand, CleverOperandKind, CleverRegister, ConditionCode,
    },
    traits::{Address, InsnRead},
};
use lru_time_cache::LruCache;

use crate::{
    error::{AccessKind, CPUException, CPUResult, FaultCharacteristics, FaultStatus},
    io::IOBus,
    mem::{MemoryBus, MemoryController},
    page::PageEntry,
    reg::{Flags, Mode, RegsRaw},
};

use bytemuck::{Pod, Zeroable};

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Status {
    Enabled,
    Active,
    Halted,
    Interrupted,
}

#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum CpuExecutionMode {
    Supervisor = 0,
    User = 1,
}

pub struct CPU {
    bus: Arc<MemoryBus>,
    ioports: IOBus,
    regs: RegsRaw,
    pcache: RefCell<LruCache<i64, u64>>,
    pending_exceptions: VecDeque<CPUException>,
    status: Status,
    handling_exception: Option<CPUException>,
    // L1 I-cache
    icache: RefCell<LruCache<i64, [u16; 16]>>,
    pcache_invalid: bool,
}

#[inline]
fn ss_to_shift(ss: u16) -> u32 {
    8u32.wrapping_shl(ss as u32)
}

#[inline]
fn ss_to_mask(ss: u16) -> u64 {
    2u64.wrapping_shl(8u32.wrapping_shl(ss as u32).wrapping_sub(1))
        .wrapping_sub(1)
}

#[inline]
fn ss_to_size(ss: u16) -> usize {
    1usize.wrapping_shl(ss as u32)
}

#[inline]
fn signex_ss(ss: u16, val: u64) -> u64 {
    let shift = 64 - ss_to_shift(ss);
    let x = (val & ss_to_mask(ss)) as i64;

    ((x << shift) >> shift) as u64
}

bitflags::bitflags! {
    #[derive(Zeroable, Pod)]
    #[repr(transparent)]
    pub struct ItabFlags : u64{
        const PX = 0x01;
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Zeroable, Pod)]
#[repr(C)]
pub struct ItabEntry {
    pub ip: i64,
    pub sp: u64,
    pub flags: ItabFlags,
    #[doc(hidden)]
    pub __reserved: u64,
}

fn do_arith_logic<F: FnOnce(u64, u64) -> (u64, bool)>(
    a: u64,
    b: u64,
    ss: u16,
    f: F,
) -> (u64, Flags) {
    let (res, roverflow) = f(a, b);

    let masked_result = res & ss_to_mask(ss);
    let delta_sign = (a.wrapping_shr(ss_to_shift(ss) - 1)
        ^ masked_result.wrapping_shr(ss_to_shift(ss) - 1))
        != 0;

    let carry = roverflow || (res.wrapping_shr(ss_to_shift(ss)) != 0);

    let mut flags = Flags::empty();
    if masked_result == 0 {
        flags |= Flags::Z;
    }
    if masked_result.count_ones() & 1 == 1 {
        flags |= Flags::P;
    }
    if masked_result.wrapping_shr(ss_to_shift(ss) - 1) == 1 {
        flags |= Flags::N;
    }

    if delta_sign != carry {
        flags |= Flags::V;
    }

    if carry {
        flags |= Flags::C;
    }
    (masked_result, flags)
}

fn compute_flags_from_val(x: u64, ss: u16) -> Flags {
    let mut flags = Flags::empty();
    if x == 0 {
        flags |= Flags::Z;
    }
    if x.count_ones() & 1 == 1 {
        flags |= Flags::P;
    }
    if x.wrapping_shr(ss_to_shift(ss) - 1) == 1 {
        flags |= Flags::N;
    }
    flags
}

impl CPU {
    pub fn new(mem: Arc<MemoryBus>, io: IOBus) -> CPU {
        CPU {
            bus: mem,
            ioports: io,
            regs: RegsRaw::new(),
            pcache: RefCell::new(LruCache::with_capacity(1024)),
            pending_exceptions: VecDeque::new(),
            status: Status::Enabled,
            icache: RefCell::new(LruCache::with_capacity(1024)),
            pcache_invalid: false,
            handling_exception: None,
        }
    }

    fn current_mode(&self) -> CpuExecutionMode {
        unsafe { core::mem::transmute(self.regs.mode.contains(Mode::XM)) }
    }

    fn resolve_vaddr_in(
        &self,
        vaddr: i64,
        bus: &MemoryController,
        access: AccessKind,
    ) -> CPUResult<u64> {
        let mode_status = match self.current_mode() {
            CpuExecutionMode::Supervisor => FaultStatus::empty(),
            CpuExecutionMode::User => FaultStatus::STATUS_USER,
        };
        if self.regs.cr[0] & 0x01 == 0 {
            if (vaddr & 0xffffffff) != vaddr {
                Err(CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        pref: (vaddr as u64),
                        flevel: 0,
                        access_kind: access,
                        status: mode_status
                            | FaultStatus::STATUS_NON_PAGED
                            | FaultStatus::STATUS_NON_CANONICAL,
                        ..Zeroable::zeroed()
                    },
                ))
            } else {
                Ok(vaddr as u64)
            }
        } else {
            let mut pagetbl = self.regs.cr[1];

            let (level, leading_bits) = match (self.regs.cr[0] & 0x38) >> 3 {
                0 => (3, 32),
                1 => (4, 24),
                2 => (4, 16),
                3 => (5, 8),
                4 => (6, 0),
                val @ 5..=7 => panic!(
                    "Consistency Check Failed: cr0.PTL expected value in 0..=4, but got {}",
                    val
                ),
                _ => unsafe { core::hint::unreachable_unchecked() },
            };

            if (vaddr.leading_zeros() + vaddr.leading_ones()) <= leading_bits {
                return Err(CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        pref: (vaddr as u64),
                        flevel: 0,
                        access_kind: access,
                        status: mode_status | FaultStatus::STATUS_NON_CANONICAL,
                        ..Zeroable::zeroed()
                    },
                ));
            }

            let mask = (!0u64).wrapping_shr(leading_bits);

            let addr = (vaddr as u64) & mask;

            let page_offset = addr & 0xfff;
            let mut page_index = addr >> 12;

            if (pagetbl & 0xfff) != 0 {
                return Err(CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        pref: (vaddr as u64),
                        flevel: level,
                        access_kind: access,
                        status: mode_status | FaultStatus::STATUS_VALIDATION_ERROR,
                        ..Zeroable::zeroed()
                    },
                ));
            } else {
                for i in (0..level).rev() {
                    let tbl_index = page_index & 0x1ff;
                    page_index >>= 9;

                    let addr = pagetbl | (tbl_index << 3);
                    let page = bus.read::<PageEntry>(addr)?;
                    page.check_access(access, i, vaddr, self.current_mode())?;
                    pagetbl = page.value();
                }
                Ok(pagetbl | page_offset)
            }
        }
    }

    fn read_bytes_aligned_in(
        &self,
        mut vaddr: i64,
        access: AccessKind,
        buf: &mut [u8],
        bus: &MemoryController,
    ) -> CPUResult<()> {
        assert!(buf.len() < 0x4096);
        let paddr = self.resolve_vaddr_in(vaddr, bus, access)?;
        bus.read_bytes(buf, paddr)
    }

    fn read_bytes_in(
        &self,
        mut vaddr: i64,
        access: AccessKind,
        buf: &mut [u8],
        bus: &MemoryController,
    ) -> CPUResult<()> {
        if self.regs.cr[0] & 0x1 == 0 {
            return bus.read_bytes(buf, self.resolve_vaddr_in(vaddr, bus, access)?);
            // resolve_vaddr_in is just to avoid duplicating Physical Addr Range Checks
        }

        let avail = (0x1000 - (vaddr & 0xfff)) as usize;
        let mut len = buf.len();
        if len <= avail {
            let addr = self.resolve_vaddr_in(vaddr, bus, access)?;
            bus.read_bytes(buf, addr)
        } else {
            let mut addr = self.resolve_vaddr_in(vaddr, bus, access)?;
            vaddr += avail as i64;
            let (mut first, mut rest) = buf.split_at_mut(avail);
            bus.read_bytes(first, addr)?;
            len -= avail;
            while len >= 4096 {
                addr = self.resolve_vaddr_in(vaddr, bus, access)?;
                vaddr += 4096;
                len -= 4096;
                (first, rest) = rest.split_at_mut(4096);

                bus.read_bytes(first, addr)?;
            }
            if len != 0 {
                addr = self.resolve_vaddr_in(vaddr, bus, access)?;
                bus.read_bytes(rest, addr)
            } else {
                Ok(())
            }
        }
    }

    fn write_bytes_aligned_in(
        &self,
        mut vaddr: i64,
        buf: &[u8],
        bus: &mut MemoryController,
    ) -> CPUResult<()> {
        assert!(buf.len() < 0x4096);
        let paddr = self.resolve_vaddr_in(vaddr, bus, AccessKind::Write)?;
        bus.write_bytes(buf, paddr)
    }

    fn write_bytes_in(
        &self,
        mut vaddr: i64,
        buf: &[u8],
        bus: &mut MemoryController,
    ) -> CPUResult<()> {
        let access = AccessKind::Write;
        if self.regs.cr[0] & 0x1 == 0 {
            return bus.write_bytes(buf, self.resolve_vaddr_in(vaddr, bus, access)?);
            // resolve_vaddr_in is just to avoid duplicating Physical Addr Range Checks
        }

        let avail = (0x1000 - (vaddr & 0xfff)) as usize;
        let mut len = buf.len();
        if len <= avail {
            let addr = self.resolve_vaddr_in(vaddr, bus, access)?;
            bus.write_bytes(buf, addr)
        } else {
            let mut addr = self.resolve_vaddr_in(vaddr, bus, access)?;
            vaddr += avail as i64;
            let (mut first, mut rest) = buf.split_at(avail);
            bus.write_bytes(first, addr)?;
            len -= avail;
            while len >= 4096 {
                addr = self.resolve_vaddr_in(vaddr, bus, access)?;
                vaddr += 4096;
                len -= 4096;
                (first, rest) = rest.split_at(4096);

                bus.write_bytes(first, addr)?;
            }
            if len != 0 {
                addr = self.resolve_vaddr_in(vaddr, bus, access)?;
                bus.write_bytes(rest, addr)
            } else {
                Ok(())
            }
        }
    }

    fn read_in<T: Pod>(
        &self,
        vaddr: i64,
        access: AccessKind,
        bus: &MemoryController,
    ) -> CPUResult<T> {
        let mut ret = T::zeroed();
        self.read_bytes_in(vaddr, access, bytemuck::bytes_of_mut(&mut ret), bus)?;
        Ok(ret)
    }

    fn read_aligned_in<T: Pod>(
        &self,
        vaddr: i64,
        access: AccessKind,
        bus: &MemoryController,
    ) -> CPUResult<T> {
        let mut ret = T::zeroed();
        self.read_bytes_aligned_in(vaddr, access, bytemuck::bytes_of_mut(&mut ret), bus)?;
        Ok(ret)
    }

    fn write_in<T: Pod>(&self, vaddr: i64, bus: &mut MemoryController, val: T) -> CPUResult<()> {
        self.write_bytes_in(vaddr, bytemuck::bytes_of(&val), bus)
    }

    fn write_aligned_in<T: Pod>(
        &self,
        vaddr: i64,
        bus: &mut MemoryController,
        val: T,
    ) -> CPUResult<()> {
        self.write_bytes_aligned_in(vaddr, bytemuck::bytes_of(&val), bus)
    }

    pub fn read<T: Pod>(&self, vaddr: i64, access: AccessKind) -> CPUResult<T> {
        self.bus
            .with_unlocked_bus(|bus| self.read_in(vaddr, access, bus))
    }

    pub fn read_bytes(&self, vaddr: i64, access: AccessKind, buf: &mut [u8]) -> CPUResult<()> {
        self.bus
            .with_unlocked_bus(|bus| self.read_bytes_in(vaddr, access, buf, bus))
    }

    pub fn read_aligned<T: Pod>(&self, vaddr: i64, access: AccessKind) -> CPUResult<T> {
        self.bus
            .with_unlocked_bus(|bus| self.read_aligned_in(vaddr, access, bus))
    }

    pub fn write<T: Pod>(&self, vaddr: i64, val: T) -> CPUResult<()> {
        self.bus
            .with_locked_bus(|bus| self.write_in(vaddr, bus, val))
    }

    pub fn write_bytes(&self, vaddr: i64, buf: &[u8]) -> CPUResult<()> {
        self.bus
            .with_locked_bus(|bus| self.write_bytes_in(vaddr, buf, bus))
    }

    pub fn write_aligned<T: Pod>(&self, vaddr: i64, val: T) -> CPUResult<()> {
        self.bus
            .with_locked_bus(|bus| self.write_aligned_in(vaddr, bus, val))
    }

    pub fn push<T: Pod>(&mut self, val: T) -> CPUResult<()> {
        self.regs.gprs[7] += ((u64::try_from(core::mem::size_of::<T>()).unwrap() + 7) / 8) * 8;
        self.write(self.regs.gprs[7] as i64, val)
    }

    pub fn pop<T: Pod>(&mut self) -> CPUResult<T> {
        let val = self.read(self.regs.gprs[7] as i64, AccessKind::Access)?;
        self.regs.gprs[7] -= ((u64::try_from(core::mem::size_of::<T>()).unwrap() + 7) / 8) * 8;
        Ok(val)
    }

    pub fn fetch_iword(&mut self) -> CPUResult<u16> {
        let icache_line = self.regs.ip & !0x1f;
        let offset = ((self.regs.ip & 0x1f) >> 1) as usize;
        self.regs.ip += 2;
        if let Some(line) = self.icache.get_mut().get(&icache_line) {
            Ok(line[offset])
        } else {
            let line = self.read_aligned(icache_line, AccessKind::Execute)?;
            self.icache.get_mut().insert(icache_line, line);

            Ok(line[offset])
        }
    }

    pub fn get_regs_mut(&mut self) -> &mut RegsRaw {
        &mut self.regs
    }

    pub fn get_regs(&self) -> &RegsRaw {
        &self.regs
    }

    pub fn poll_exceptions(&mut self) -> CPUResult<()> {
        if self.status == Status::Interrupted {
            self.status = Status::Active;
            return Ok(());
        }
        if let Some(mut except) = self.pending_exceptions.pop_front() {
            match self.handling_exception {
                Some(CPUException::Abort | CPUException::Reset) => except = CPUException::Reset,
                Some(_) => except = CPUException::Abort,
                None => {}
            }
            self.handling_exception = Some(except);
            match (|| -> CPUResult<()> {
                let itab_addr = self.regs.cr[6] as i64;
                let index = match except {
                    CPUException::Abort => {
                        self.regs.crx[0] = 0;
                        0
                    }
                    CPUException::Undefined => 1,
                    CPUException::SystemProtection(code) => {
                        self.regs.crx[0] = code;
                        2
                    }
                    CPUException::PageFault(vaddr, char) => {
                        self.regs.crx[0] = vaddr as u64;
                        match self.regs.crx[1] {
                            0 => {}
                            addr => {
                                self.write(addr as i64, char)?;
                            }
                        }
                        3
                    }
                    CPUException::ExecutionAlignment(vaddr) => {
                        self.regs.crx[0] = vaddr as u64;
                        4
                    }
                    CPUException::NonMaskableInterrupt => 5,
                    CPUException::FloatingPointException(fpe) => {
                        if self.regs.cr[0] & 0x80 == 0 {
                            self.regs.crx[0] = 0;
                            2
                        } else {
                            self.regs.crx[0] = fpe.bits() as u64;
                            6
                        }
                    }
                    CPUException::Reset => Err(CPUException::Reset)?,
                };
                let extent = self.read_aligned::<u64>(itab_addr, AccessKind::Access)?;
                if extent < ((index + 32) * 32) {
                    Err(CPUException::Abort)?
                }

                let ientry_addr = itab_addr + 32 + ((index as i64) * 32);

                let ientry = self.read_aligned::<ItabEntry>(ientry_addr, AccessKind::Access)?;

                let saved_sp = self.regs.gprs[7];

                self.regs.gprs[7] = ientry.sp;

                self.push(saved_sp)?;
                self.push(self.regs.mode)?;
                self.push(self.regs.ip)?;

                if ientry.ip & !1 != 0 {
                    Err(CPUException::Abort)?
                }

                self.regs.ip = ientry.ip;
                Ok(())
            })() {
                Ok(()) => {
                    self.status = Status::Interrupted;
                    Ok(())
                }
                Err(CPUException::Reset) => Err(CPUException::Reset),
                Err(_) if except == CPUException::Abort => Err(CPUException::Reset),
                Err(_) => Err(CPUException::Abort),
            }
        } else {
            Ok(())
        }
    }

    fn check_extension(&self, ext: CleverExtension) -> CPUResult<()> {
        match ext {
            CleverExtension::Main => Ok(()),
            #[cfg(feature = "float")]
            CleverExtension::Float => {
                if self.regs.cr[0] & 0x40 != 0 {
                    Ok(())
                } else {
                    Err(CPUException::Undefined)
                }
            }
            #[cfg(feature = "float-ext")]
            CleverExtension::FloatExt => {
                if self.regs.cr[0] & 0x40 != 0 {
                    Ok(())
                } else {
                    Err(CPUException::Undefined)
                }
            }
            #[cfg(feature = "vector")]
            CleverExtension::Vec => {
                if self.regs.cr[0] & 0x100 != 0 {
                    Ok(())
                } else {
                    Err(CPUException::Undefined)
                }
            }
            #[cfg(feature = "rand")]
            CleverExtension::Rand => Ok(()),
            _ => Err(CPUException::Undefined),
        }
    }

    fn fetch_insn(&mut self) -> CPUResult<CleverInstruction> {
        let iword = self.fetch_iword()?;
        let opc = if let Some(insn) = CleverOpcode::from_opcode(iword.to_be()) {
            insn
        } else {
            return Err(CPUException::Undefined);
        };
        self.check_extension(opc.extension())?;
        match opc.operands() {
            CleverOperandKind::Insn => {
                let mut insn = self.fetch_insn()?;
                if let Some(prefix) = insn.prefix() {
                    return Err(CPUException::Undefined);
                }
                match (opc, insn.opcode()) {
                    (
                        CleverOpcode::Repbc { .. } | CleverOpcode::Repbi { .. },
                        CleverOpcode::Bcpy { .. }
                        | CleverOpcode::Bsto { .. }
                        | CleverOpcode::Bsca { .. }
                        | CleverOpcode::Bcmp { .. }
                        | CleverOpcode::Btst { .. }
                        | CleverOpcode::In { .. }
                        | CleverOpcode::Out { .. },
                    )
                    | (
                        CleverOpcode::Vec { .. },
                        CleverOpcode::Mov
                        | CleverOpcode::MovRD { .. }
                        | CleverOpcode::MovRS { .. }
                        | CleverOpcode::Add { .. }
                        | CleverOpcode::AddRD { .. }
                        | CleverOpcode::AddRS { .. }
                        | CleverOpcode::Sub { .. }
                        | CleverOpcode::SubRD { .. }
                        | CleverOpcode::SubRS { .. }
                        | CleverOpcode::And { .. }
                        | CleverOpcode::AndRD { .. }
                        | CleverOpcode::AndRS { .. }
                        | CleverOpcode::Or { .. }
                        | CleverOpcode::OrRD { .. }
                        | CleverOpcode::OrRS { .. }
                        | CleverOpcode::Xor { .. }
                        | CleverOpcode::XorRD { .. }
                        | CleverOpcode::XorRS { .. }
                        | CleverOpcode::BNot { .. }
                        | CleverOpcode::Neg { .. }
                        | CleverOpcode::FAbs { .. }
                        | CleverOpcode::Round { .. }
                        | CleverOpcode::Ceil { .. }
                        | CleverOpcode::Floor { .. }
                        | CleverOpcode::FNeg { .. }
                        | CleverOpcode::FInv { .. }
                        | CleverOpcode::FAdd { .. }
                        | CleverOpcode::FSub { .. }
                        | CleverOpcode::FMul { .. }
                        | CleverOpcode::FDiv { .. }
                        | CleverOpcode::FRem { .. }
                        | CleverOpcode::FFma { .. }
                        | CleverOpcode::Exp { .. }
                        | CleverOpcode::Ln { .. }
                        | CleverOpcode::Lg { .. }
                        | CleverOpcode::Sin { .. }
                        | CleverOpcode::Cos { .. }
                        | CleverOpcode::Tan { .. }
                        | CleverOpcode::Asin { .. }
                        | CleverOpcode::Acos { .. }
                        | CleverOpcode::Atan { .. }
                        | CleverOpcode::Exp2 { .. }
                        | CleverOpcode::Log10 { .. }
                        | CleverOpcode::Lnp1 { .. }
                        | CleverOpcode::Expm1 { .. }
                        | CleverOpcode::Sqrt { .. },
                    ) => {}
                    _ => return Err(CPUException::Undefined),
                }

                insn.set_prefix(opc);
                Ok(insn)
            }
            CleverOperandKind::AbsAddr => {
                let size = opc.branch_width().unwrap() - 1;
                let num_iwords = 1 << (size as u32);
                let mut addr = 0u64;
                for i in 0..num_iwords {
                    let iword = self.fetch_iword()? as u64;
                    addr |= iword << (16 * i);
                }
                let op = CleverOperand::Immediate(CleverImmediate::Long(num_iwords << 1, addr));

                Ok(CleverInstruction::new(opc, vec![op]))
            }
            CleverOperandKind::RelAddr => {
                let size = opc.branch_width().unwrap() - 1;
                let num_iwords = 1 << (size as u32);
                let mut addr = 0i64;
                for i in 0..num_iwords {
                    let iword = self.fetch_iword()? as i64;
                    addr |= iword << (16 * i);
                }
                addr = signex_ss(size + 1, addr as u64) as i64;
                let op = CleverOperand::Immediate(CleverImmediate::LongRel(num_iwords << 1, addr));

                Ok(CleverInstruction::new(opc, vec![op]))
            }
            CleverOperandKind::Normal(n) => {
                let mut ops = Vec::with_capacity(n as usize);
                for _ in 0..n {
                    let op = self.fetch_iword()?.to_be();
                    let op = match op >> 14 {
                        0b00 => {
                            let reg = CleverRegister((op & 0xff) as u8);
                            if op & 0x2000 != 0 {
                                let size = 1 << ((op >> 8) & 0xf);
                                if size > 128 {
                                    return Err(CPUException::Undefined);
                                }
                                if (op & 0x1000) != 0 {
                                    return Err(CPUException::Undefined);
                                }
                                self.check_extension(CleverExtension::Vec)?;
                                CleverOperand::VecPair { size, lo: reg }
                            } else {
                                let size = 1 << ((op >> 8) & 0x3);
                                if (op & 0x1C00) != 0 {
                                    return Err(CPUException::Undefined);
                                }
                                CleverOperand::Register { size, reg }
                            }
                        }
                        0b01 => {
                            let base = CleverRegister((op & 0xf) as u8);
                            let size = 1 << ((op >> 4) & 0x3);
                            let scale = 1 << ((op >> 7) & 0x7);

                            let index = if op & 0x80 != 0 {
                                CleverIndex::Abs((((op << 2) & 0xF000) as i16) >> 12)
                            } else {
                                CleverIndex::Register(CleverRegister(((op >> 10) & 0xf) as u8))
                            };
                            CleverOperand::Indirect {
                                size,
                                base,
                                scale,
                                index,
                            }
                        }
                        0b10 => {
                            if (op & 0x1000) != 0 {
                                CleverOperand::Immediate(CleverImmediate::ShortRel(
                                    ((op as i16) << 4) >> 4,
                                ))
                            } else {
                                CleverOperand::Immediate(CleverImmediate::Short(op & 0xfff))
                            }
                        }
                        0b11 => {
                            let ss = ((op >> 8) & 0x3) + 1;
                            let size = 1 << ss;
                            if size == 128 {
                                self.check_extension(CleverExtension::Vec)?;
                            }
                            let rel = (op & 0x400) != 0;
                            let mem = (op & 0x2000) != 0;
                            if (rel | mem) && size == 128 {
                                return Err(CPUException::Undefined);
                            }
                            let reserved_mask = 0x180F | if mem { 0 } else { 0xF0 };
                            if (op & reserved_mask) != 0 {
                                self.check_extension(CleverExtension::Vec)?;
                            }

                            let zize = (op >> 4) & 0xf;

                            if zize > 128 {
                                return Err(CPUException::Undefined);
                            } else if zize > 64 {
                                self.check_extension(CleverExtension::Vec)?;
                            }

                            let mut val = 0u64;
                            let iwords = size >> 1;
                            for i in 0..iwords {
                                let iword = self.fetch_iword()?;
                                val |= (iword as u64) << (i * 16);
                            }
                            if rel {
                                val = signex_ss(ss, val);
                            }

                            let imm = match (rel, mem) {
                                (true, true) => CleverImmediate::LongMemRel(
                                    size,
                                    Address::Disp(val as i64),
                                    zize,
                                ),
                                (true, false) => CleverImmediate::LongRel(size, val as i64),
                                (false, true) => {
                                    CleverImmediate::LongMem(size, Address::Abs(val as u128), zize)
                                }
                                (false, false) => CleverImmediate::Long(size, val),
                            };
                            CleverOperand::Immediate(imm)
                        }
                        _ => unsafe { core::hint::unreachable_unchecked() },
                    };
                    ops.push(op);
                }
                Ok(CleverInstruction::new(opc, ops))
            }
        }
    }

    fn check_read(&self, op: &CleverOperand) -> CPUResult<()> {
        match op {
            CleverOperand::Register { size, reg } => {
                self.check_extension(reg.extension().ok_or(CPUException::Undefined)?)?;
                if reg.0 < 128 {
                    Ok(())
                } else if (148..155).contains(&reg.0) {
                    Err(CPUException::Undefined)
                } else if !self.regs.mode.contains(Mode::XM) {
                    Ok(())
                } else if (136..144).contains(&reg.0) {
                    let off = reg.0 - 136;
                    let bit = 1u64 << off;
                    if (self.regs.cr[7] & bit) != 0 {
                        Err(CPUException::SystemProtection(0))
                    } else {
                        Ok(())
                    }
                } else {
                    Err(CPUException::SystemProtection(0))
                }
            }
            CleverOperand::Indirect { .. } => Ok(()),
            CleverOperand::VecPair { size, lo } => {
                self.check_extension(lo.extension().ok_or(CPUException::Undefined)?)?;

                if lo.0 & 1 != 0 {
                    Err(CPUException::Undefined)
                } else if !(64..96).contains(&lo.0) {
                    Err(CPUException::Undefined)
                } else {
                    Ok(())
                }
            }
            CleverOperand::Immediate(_) => Ok(()),
        }
    }

    fn check_write(&self, op: &CleverOperand) -> CPUResult<()> {
        match op {
            CleverOperand::Register { reg, .. } => {
                self.check_extension(reg.extension().ok_or(CPUException::Undefined)?)?;
                match *reg {
                    CleverRegister::ip
                    | CleverRegister::mode
                    | CleverRegister(136..=143)
                    | CleverRegister::rdinfo => return Err(CPUException::Undefined)?,
                    _ => (),
                }
                if reg.0 < 128 {
                    Ok(())
                } else if (148..155).contains(&reg.0) {
                    Err(CPUException::Undefined)
                } else if !self.regs.mode.contains(Mode::XM) {
                    Ok(())
                } else if (136..144).contains(&reg.0) {
                    Err(CPUException::Undefined)
                } else {
                    Err(CPUException::SystemProtection(0))
                }
            }
            CleverOperand::Indirect { .. } => Ok(()),
            CleverOperand::VecPair { lo, .. } => {
                self.check_extension(lo.extension().ok_or(CPUException::Undefined)?)?;

                if lo.0 & 1 != 0 {
                    Err(CPUException::Undefined)
                } else if !(64..96).contains(&lo.0) {
                    Err(CPUException::Undefined)
                } else {
                    Ok(())
                }
            }
            CleverOperand::Immediate(
                CleverImmediate::LongMem(_, _, _) | CleverImmediate::LongMemRel(_, _, _),
            ) => Ok(()),
            CleverOperand::Immediate(imm) => Err(CPUException::Undefined),
        }
    }

    fn check_memory(&self, op: &CleverOperand) -> CPUResult<()> {
        match op {
            CleverOperand::Indirect { .. } => Ok(()),
            CleverOperand::Immediate(
                CleverImmediate::LongMem(_, _, _) | CleverImmediate::LongMemRel(_, _, _),
            ) => Ok(()),
            _ => Err(CPUException::Undefined),
        }
    }

    fn check_register_arith(&self, op: &CleverOperand) -> CPUResult<()> {
        match op {
            CleverOperand::Register { reg, .. } => {
                if !((0..16).contains(&reg.0) || (64..96).contains(&reg.0)) {
                    Err(CPUException::Undefined)
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }

    fn check_only_one_memory(&self, ops: &[CleverOperand]) -> CPUResult<()> {
        let mut has_mem = false;
        for op in ops {
            match op {
                CleverOperand::Indirect { .. }
                | CleverOperand::Immediate(
                    CleverImmediate::LongMem(_, _, _) | CleverImmediate::LongMemRel(_, _, _),
                ) => {
                    if has_mem {
                        return Err(CPUException::Undefined);
                    }
                    has_mem = true
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn read_u64_by_size_in(&self, op: &CleverOperand, bus: &MemoryController) -> CPUResult<u64> {
        match op {
            CleverOperand::Register { size, reg } => {
                let ss = match size {
                    8 => 0,
                    16 => 1,
                    32 => 2,
                    64 => 3,
                    size => unreachable!("Invalid register size {:?}", size),
                };
                let raw_val = self.regs[reg.0 as u16];

                Ok(raw_val & ss_to_mask(ss))
            }
            CleverOperand::VecPair { .. } => {
                panic!("Cannot use read_u64_by_size to read a vector operand")
            }
            CleverOperand::Immediate(CleverImmediate::Short(val)) => Ok((*val) as u64),
            CleverOperand::Immediate(CleverImmediate::ShortRel(val)) => {
                Ok(((*val) as i64).wrapping_add(self.regs.ip) as u64)
            }
            CleverOperand::Immediate(CleverImmediate::Long(_, val)) => Ok(*val), // already masked
            CleverOperand::Immediate(CleverImmediate::LongRel(_, val)) => {
                Ok(val.wrapping_add(self.regs.ip) as u64)
            }
            CleverOperand::Immediate(CleverImmediate::LongMem(_, Address::Abs(val), memsize)) => {
                if *memsize > 64 {
                    panic!("Cannot use read_u64_by_size to read a vector operand")
                }
                let byte_count = ((*memsize) >> 3) as usize;
                let addr = u64::try_from(*val).unwrap() as i64;
                let mut bytes = [0u8; 8];
                self.read_bytes_in(addr, AccessKind::Access, &mut bytes[..byte_count], bus)?;

                Ok(u64::from_le_bytes(bytes))
            }
            CleverOperand::Immediate(CleverImmediate::LongMemRel(
                _,
                Address::Disp(disp),
                memsize,
            )) => {
                if *memsize > 64 {
                    panic!("Cannot use read_u64_by_size to read a vector operand")
                }
                let byte_count = ((*memsize) >> 3) as usize;
                let addr = (*disp) + self.regs.ip;
                let mut bytes = [0u8; 8];
                self.read_bytes_in(addr, AccessKind::Access, &mut bytes[..byte_count], bus)?;

                Ok(u64::from_le_bytes(bytes))
            }
            CleverOperand::Indirect {
                size,
                base,
                scale,
                index,
            } => {
                let byte_count = ((*size) >> 3) as usize;
                let mut addr = (self.regs[base.0 as u16] as i64)
                    + (*scale as i64)
                        * match index {
                            CleverIndex::Abs(v) => *v as i64,
                            CleverIndex::Register(idx) => self.regs[idx.0 as u16] as i64,
                        };
                let mut bytes = [0u8; 8];
                self.read_bytes_in(addr, AccessKind::Access, &mut bytes[..byte_count], bus)?;

                Ok(u64::from_le_bytes(bytes))
            }
            _ => unreachable!(),
        }
    }

    fn read_u64_by_size(&self, op: &CleverOperand) -> CPUResult<u64> {
        self.bus
            .with_unlocked_bus(|bus| self.read_u64_by_size_in(op, bus))
    }

    fn write_u64_by_size_in(
        &mut self,
        op: &CleverOperand,
        bus: &mut MemoryController,
        val: u64,
    ) -> CPUResult<()> {
        match op {
            CleverOperand::Register { size, reg } => {
                let ss = match size {
                    8 => 0,
                    16 => 1,
                    32 => 2,
                    64 => 3,
                    size => unreachable!("Invalid register size {:?}", size),
                };
                let mut raw_val = val & ss_to_mask(ss);

                match *reg {
                    CleverRegister::flags => {
                        let cflags = self.regs.flags.bits() & !ss_to_mask(ss);
                        raw_val = cflags | (raw_val & Flags::all().bits());
                    }
                    CleverRegister::fpcw => {
                        if (raw_val & ((1 << 26) - 1)) != 0 {
                            return Err(CPUException::Undefined);
                        }
                    }
                    CleverRegister::cr0 => {
                        let mut mask = 0x3f;
                        #[cfg(feature = "float")]
                        {
                            mask |= 0xC0;
                        }
                        #[cfg(feature = "vector")]
                        {
                            mask |= 0x100;
                        }
                        #[cfg(feature = "rand")]
                        {
                            mask |= 0x300;
                        }

                        if (raw_val & mask) != 0 {
                            return Err(CPUException::Undefined);
                        }
                        if (raw_val & 1) != 0 {
                            self.pcache_invalid = true;
                        }
                    }
                    CleverRegister::cr3 => {
                        self.pcache_invalid = true;
                    }
                    _ => {}
                }

                self.regs[reg.0 as u16] = raw_val;

                Ok(())
            }
            CleverOperand::VecPair { .. } => {
                panic!("Cannot use read_u64_by_size to read a vector operand")
            }
            CleverOperand::Immediate(CleverImmediate::LongMem(_, Address::Abs(val), memsize)) => {
                if *memsize > 64 {
                    panic!("Cannot use read_u64_by_size to read a vector operand");
                }
                let byte_count = ((*memsize) >> 3) as usize;
                let addr = u64::try_from(*val).unwrap() as i64;
                let bytes = val.to_le_bytes();
                self.write_bytes_in(addr, &bytes[..byte_count], bus)
            }
            CleverOperand::Immediate(CleverImmediate::LongMemRel(
                _,
                Address::Disp(disp),
                memsize,
            )) => {
                if *memsize > 64 {
                    panic!("Cannot use read_u64_by_size to read a vector operand")
                }
                let byte_count = ((*memsize) >> 3) as usize;
                let addr = (*disp) + self.regs.ip;
                let bytes = val.to_le_bytes();
                self.write_bytes_in(addr, &bytes[..byte_count], bus)
            }
            CleverOperand::Indirect {
                size,
                base,
                scale,
                index,
            } => {
                let byte_count = ((*size) >> 3) as usize;
                let mut addr = (self.regs[base.0 as u16] as i64)
                    + (*scale as i64)
                        * match index {
                            CleverIndex::Abs(v) => *v as i64,
                            CleverIndex::Register(idx) => self.regs[idx.0 as u16] as i64,
                        };
                let bytes = val.to_le_bytes();
                self.write_bytes_in(addr, &bytes[..byte_count], bus)
            }
            _ => unreachable!(),
        }
    }

    fn write_u64_by_size(&mut self, op: &CleverOperand, val: u64) -> CPUResult<()> {
        let bus = self.bus.clone();

        bus.with_locked_bus(|bus| self.write_u64_by_size_in(op, bus, val))
    }

    fn compute_addr(&self, op: &CleverOperand) -> CPUResult<i64> {
        match op {
            CleverOperand::Indirect {
                base, scale, index, ..
            } => Ok(self.regs[*base] as i64
                + ((*scale as i64)
                    * match index {
                        CleverIndex::Abs(val) => *val as i64,
                        CleverIndex::Register(reg) => self.regs[*reg] as i64,
                    })),
            CleverOperand::Immediate(CleverImmediate::LongMem(_, Address::Abs(addr), _)) => {
                Ok(*addr as u64 as i64)
            }
            CleverOperand::Immediate(CleverImmediate::LongMemRel(_, Address::Disp(addr), _)) => {
                Ok((*addr) + self.regs.ip)
            }
            _ => return Err(CPUException::Undefined),
        }
    }

    fn test_cc(&self, cc: ConditionCode, flags: Flags) -> bool {
        match cc {
            ConditionCode::Parity => flags.contains(Flags::P),
            ConditionCode::Carry => flags.contains(Flags::C),
            ConditionCode::Overflow => flags.contains(Flags::V),
            ConditionCode::Zero => flags.contains(Flags::Z),
            ConditionCode::LessThan => flags.contains(Flags::V) != flags.contains(Flags::N),
            ConditionCode::LessEq => {
                (flags.contains(Flags::V) != flags.contains(Flags::N)) || flags.contains(Flags::Z)
            }
            ConditionCode::BelowEq => flags.contains(Flags::C) || flags.contains(Flags::Z),
            ConditionCode::Minus => flags.contains(Flags::N),
            ConditionCode::Plus => flags.contains(Flags::P),
            ConditionCode::Above => !(flags.contains(Flags::C) || flags.contains(Flags::Z)),
            ConditionCode::Greater => {
                (flags.contains(Flags::V) == flags.contains(Flags::N)) && !flags.contains(Flags::Z)
            }
            ConditionCode::GreaterEq => flags.contains(Flags::V) == flags.contains(Flags::N),
            ConditionCode::NotZero => !flags.contains(Flags::Z),
            ConditionCode::NoOverflow => !flags.contains(Flags::V),
            ConditionCode::NoCarry => !flags.contains(Flags::C),
            ConditionCode::NoParity => !flags.contains(Flags::P),
        }
    }

    pub fn step(&mut self) -> CPUResult<()> {
        self.poll_exceptions()?;
        let insn = self.fetch_insn()?;

        if let Some(CleverOpcode::Vec { .. }) = insn.prefix() {
            todo!("Vec prefix needs special handling")
        }

        match insn.opcode() {
            CleverOpcode::Add { lock, flags } => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_register_arith(dest)?;
                self.check_register_arith(dest)?;
                self.check_write(dest)?;
                self.check_read(src)?;
                let dest_ss = dest.size_ss().unwrap();
                let calc_ss = dest.size_ss().unwrap().max(src.size_ss().unwrap());
                let res_flags = if lock {
                    let bus = self.bus.clone();
                    bus.with_locked_bus(|bus| -> CPUResult<Flags> {
                        self.check_memory(dest)?;
                        let (a, b) = (
                            self.read_u64_by_size_in(dest, bus)?,
                            self.read_u64_by_size_in(src, bus)?,
                        );
                        let (res, flags) = do_arith_logic(a, b, calc_ss, u64::overflowing_add);
                        self.write_u64_by_size_in(dest, bus, ss_to_mask(dest_ss) & res)?;
                        Ok(flags)
                    })?
                } else {
                    let (a, b) = (self.read_u64_by_size(dest)?, self.read_u64_by_size(src)?);
                    let (res, flags) = do_arith_logic(a, b, dest_ss, u64::overflowing_add);
                    self.write_u64_by_size(dest, ss_to_mask(dest_ss) & res)?;
                    flags
                };

                if flags {
                    self.regs.flags &= !(Flags::ARITH_FLAGS);
                    self.regs.flags |= res_flags;
                }
            }
            CleverOpcode::Sub { lock, flags } => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_register_arith(dest)?;
                self.check_register_arith(dest)?;
                self.check_write(dest)?;
                self.check_read(src)?;
                let dest_ss = dest.size_ss().unwrap();
                let calc_ss = dest.size_ss().unwrap().max(src.size_ss().unwrap());
                let res_flags = if lock {
                    let bus = self.bus.clone();
                    bus.with_locked_bus(|bus| -> CPUResult<Flags> {
                        self.check_memory(dest)?;
                        let (a, b) = (
                            self.read_u64_by_size_in(dest, bus)?,
                            self.read_u64_by_size_in(src, bus)?,
                        );
                        let (res, flags) = do_arith_logic(a, b, dest_ss, u64::overflowing_sub);
                        self.write_u64_by_size_in(dest, bus, res)?;
                        Ok(flags)
                    })?
                } else {
                    let (a, b) = (self.read_u64_by_size(dest)?, self.read_u64_by_size(src)?);
                    let (res, flags) = do_arith_logic(a, b, dest_ss, u64::overflowing_sub);
                    self.write_u64_by_size(dest, res)?;
                    flags
                };

                if flags {
                    self.regs.flags &= !(Flags::ARITH_FLAGS);
                    self.regs.flags |= res_flags;
                }
            }
            CleverOpcode::And { lock, flags } => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_register_arith(dest)?;
                self.check_register_arith(dest)?;
                self.check_write(dest)?;
                self.check_read(src)?;
                let dest_ss = dest.size_ss().unwrap();
                let calc_ss = dest.size_ss().unwrap().max(src.size_ss().unwrap());
                let res_flags = if lock {
                    let bus = self.bus.clone();
                    bus.with_locked_bus(|bus| -> CPUResult<Flags> {
                        self.check_memory(dest)?;
                        let (a, b) = (
                            self.read_u64_by_size_in(dest, bus)?,
                            self.read_u64_by_size_in(src, bus)?,
                        );
                        let (res, flags) = do_arith_logic(a, b, dest_ss, |a, b| (a & b, false));
                        self.write_u64_by_size_in(dest, bus, res)?;
                        Ok(flags)
                    })?
                } else {
                    let (a, b) = (self.read_u64_by_size(dest)?, self.read_u64_by_size(src)?);
                    let (res, flags) = do_arith_logic(a, b, dest_ss, |a, b| (a & b, false));
                    self.write_u64_by_size(dest, ss_to_mask(dest_ss) & res)?;
                    flags
                };

                if flags {
                    self.regs.flags &= !(Flags::ARITH_FLAGS);
                    self.regs.flags |= res_flags;
                }
            }
            CleverOpcode::Or { lock, flags } => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_register_arith(dest)?;
                self.check_register_arith(dest)?;
                self.check_write(dest)?;
                self.check_read(src)?;
                let dest_ss = dest.size_ss().unwrap();
                let calc_ss = dest.size_ss().unwrap().max(src.size_ss().unwrap());
                let res_flags = if lock {
                    let bus = self.bus.clone();
                    bus.with_locked_bus(|bus| -> CPUResult<Flags> {
                        self.check_memory(dest)?;
                        let (a, b) = (
                            self.read_u64_by_size_in(dest, bus)?,
                            self.read_u64_by_size_in(src, bus)?,
                        );
                        let (res, flags) = do_arith_logic(a, b, dest_ss, |a, b| (a | b, false));
                        self.write_u64_by_size_in(dest, bus, ss_to_mask(dest_ss) & res)?;
                        Ok(flags)
                    })?
                } else {
                    let (a, b) = (self.read_u64_by_size(dest)?, self.read_u64_by_size(src)?);
                    let (res, flags) = do_arith_logic(a, b, dest_ss, |a, b| (a | b, false));
                    self.write_u64_by_size(dest, ss_to_mask(dest_ss) & res)?;
                    flags
                };

                if flags {
                    self.regs.flags &= !(Flags::ARITH_FLAGS);
                    self.regs.flags |= res_flags;
                }
            }
            CleverOpcode::Xor { lock, flags } => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_register_arith(dest)?;
                self.check_register_arith(dest)?;
                self.check_write(dest)?;
                self.check_read(src)?;
                let dest_ss = dest.size_ss().unwrap();
                let calc_ss = dest.size_ss().unwrap().max(src.size_ss().unwrap());
                let res_flags = if lock {
                    let bus = self.bus.clone();
                    bus.with_locked_bus(|bus| -> CPUResult<Flags> {
                        self.check_memory(dest)?;
                        let (a, b) = (
                            self.read_u64_by_size_in(dest, bus)?,
                            self.read_u64_by_size_in(src, bus)?,
                        );
                        let (res, flags) = do_arith_logic(a, b, dest_ss, |a, b| (a ^ b, false));
                        self.write_u64_by_size_in(dest, bus, ss_to_mask(dest_ss) & res)?;
                        Ok(flags)
                    })?
                } else {
                    let (a, b) = (self.read_u64_by_size(dest)?, self.read_u64_by_size(src)?);
                    let (res, flags) = do_arith_logic(a, b, dest_ss, |a, b| (a ^ b, false));
                    self.write_u64_by_size(dest, ss_to_mask(dest_ss) & res)?;
                    flags
                };

                if flags {
                    self.regs.flags &= !(Flags::ARITH_FLAGS);
                    self.regs.flags |= res_flags;
                }
            }
            CleverOpcode::Mov => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_write(dest)?;
                self.check_read(src)?;
                let val = self.read_u64_by_size(src)?;
                let ss = src.size_ss().unwrap();
                let res_flags = compute_flags_from_val(val, ss);
                self.regs.flags &= !(Flags::MOV_FLAGS);
                self.regs.flags |= res_flags;
                self.write_u64_by_size(dest, val)?;
            }
            CleverOpcode::MovRD { r } => {
                let [src] = match insn.operands() {
                    [src] => [src],
                    ops => unreachable!("invalid operands {:?}", ops),
                };
                self.check_read(src)?;
                let val = self.read_u64_by_size(src)?;
                let ss = src.size_ss().unwrap_or(1); // Short-imm unsigned is ss=1
                let res_flags = compute_flags_from_val(val, ss);
                self.regs.flags &= !(Flags::MOV_FLAGS);
                self.regs.flags |= res_flags;
                self.regs[r] = val;
            }
            CleverOpcode::MovRS { r } => {
                let [dest] = match insn.operands() {
                    [dest] => [dest],
                    _ => unreachable!(),
                };
                self.check_write(dest)?;
                let val = self.regs[r];
                let res_flags = compute_flags_from_val(val, 3);
                self.regs.flags &= !(Flags::MOV_FLAGS);
                self.regs.flags |= res_flags;

                self.write_u64_by_size(dest, val)?;
            }
            CleverOpcode::Lea => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_write(dest)?;
                self.check_memory(src)?;

                let val = self.compute_addr(src)? as u64;
                self.write_u64_by_size(dest, val)?;
            }
            CleverOpcode::LeaRD { r } => {
                let [src] = match insn.operands() {
                    [src] => [src],
                    _ => unreachable!(),
                };
                let val = self.compute_addr(src)? as u64;
                self.regs[r] = val;
            }
            CleverOpcode::Nop10 { .. }
            | CleverOpcode::Nop11 { .. }
            | CleverOpcode::Nop12 { .. }
            | CleverOpcode::Nop13 { .. } => { /*no-op */ }
            CleverOpcode::Push => {
                let [src] = match insn.operands() {
                    [src] => [src],
                    _ => unreachable!(),
                };

                self.check_read(src)?;
                let val = self.read_u64_by_size(src)?;
                self.push(val)?;
            }
            CleverOpcode::Pop => {
                let [dest] = match insn.operands() {
                    [dest] => [dest],
                    _ => unreachable!(),
                };

                self.check_write(dest)?;
                let val = self.pop()?;
                self.write_u64_by_size(dest, val)?;
            }
            CleverOpcode::PushR { r } => {
                let val = self.regs[r];
                self.push(val)?;
            }
            CleverOpcode::PopR { r } => {
                let val = self.pop()?;
                self.regs[r] = val;
            }
            CleverOpcode::Stogpr => {
                let [dest] = match insn.operands() {
                    [dest] => [dest],
                    _ => unreachable!(),
                };
                let addr = self.compute_addr(dest)?;
                self.write(addr, self.regs.gprs)?;
            }
            CleverOpcode::Stoar => {
                let [dest] = match insn.operands() {
                    [dest] => [dest],
                    _ => unreachable!(),
                };
                let addr = self.compute_addr(dest)?;
                self.write(addr, *self.regs.user_registers())?;
            }
            CleverOpcode::Rstogpr => {
                let [src] = match insn.operands() {
                    [src] => [src],
                    _ => unreachable!(),
                };
                let addr = self.compute_addr(src)?;
                self.regs.gprs = self.read(addr, AccessKind::Access)?;
            }
            CleverOpcode::Rstoar => {
                let [src] = match insn.operands() {
                    [src] => [src],
                    _ => unreachable!(),
                };
                let addr = self.compute_addr(src)?;
                let mut tmp_regs: [u64; 128] = self.read(addr, AccessKind::Access)?;

                for i in 16..128 {
                    if tmp_regs[i] != self.regs.user_registers()[i] {
                        self.check_extension(
                            CleverRegister(i as u8)
                                .extension()
                                .ok_or(CPUException::Undefined)?,
                        )?;
                    }
                }

                tmp_regs[16] = self.regs.ip as u64;
                tmp_regs[18] = self.regs.mode.bits();

                *self.regs.user_registers_mut() = tmp_regs;
            }
            CleverOpcode::Pushgpr => {
                self.push(self.regs.gprs)?;
            }
            CleverOpcode::Pushar => {
                self.push(*self.regs.user_registers())?;
            }
            CleverOpcode::Popgpr => {
                self.regs.gprs = self.pop()?;
            }
            CleverOpcode::Popar => {
                let mut tmp_regs: [u64; 128] = self.pop()?;
                for i in 16..128 {
                    if tmp_regs[i] != self.regs.user_registers()[i] {
                        self.check_extension(
                            CleverRegister(i as u8)
                                .extension()
                                .ok_or(CPUException::Undefined)?,
                        )?;
                    }
                }

                tmp_regs[16] = self.regs.ip as u64;
                tmp_regs[18] = self.regs.mode.bits();

                *self.regs.user_registers_mut() = tmp_regs;
            }
            CleverOpcode::Movsx { flags } => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_write(dest)?;
                self.check_read(src)?;
                let val = self.read_u64_by_size(src)?;
                let ss = src.size_ss();

                let ext_val = match ss {
                    Some(ss) => signex_ss(ss, val),
                    None => (((val as i64) << 52) >> 52) as u64,
                };
                let res_flags = compute_flags_from_val(ext_val, dest.size_ss().unwrap());
                if flags {
                    self.regs.flags &= !(Flags::MOV_FLAGS);
                    self.regs.flags |= res_flags;
                }
                self.write_u64_by_size(dest, ext_val)?;
            }
            CleverOpcode::Bswap { flags } => {
                self.check_only_one_memory(insn.operands())?;
                let [dest, src] = match insn.operands() {
                    [dest, src] => [dest, src],
                    _ => unreachable!(),
                };
                self.check_write(dest)?;
                self.check_read(src)?;
                let (ss1, ss2) = (dest.size_ss(), src.size_ss());
                if ss1 != ss2 {
                    return Err(CPUException::Undefined);
                }
                let ss = ss1.unwrap();
                let val = self.read_u64_by_size(src)?;
                let val = val.swap_bytes() >> (64 - ss_to_shift(ss));
                let res_flags = compute_flags_from_val(val, ss);
                if flags {
                    self.regs.flags &= !(Flags::MOV_FLAGS);
                    self.regs.flags |= res_flags;
                }
                self.write_u64_by_size(dest, val)?;
            }
            CleverOpcode::Bcpy { ss } => {
                let mut src_addr = self.regs.gprs[4] as i64;
                let mut dest_addr = self.regs.gprs[5] as i64;
                let mut count = self.regs.gprs[1];
                let mut flags = self.regs.flags;
                let res = (|| -> CPUResult<()> {
                    match insn.prefix() {
                        Some(CleverOpcode::Repbi { cc }) => {
                            let mut val = [0u8; 8];
                            let size_count = 1 << ss;
                            if !self.test_cc(cc, flags) {
                                return Ok(());
                            }
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            self.write_bytes(dest_addr, &val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                if !self.test_cc(cc, flags) {
                                    return Ok(());
                                }
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val[..size_count],
                                )?;
                                self.write_bytes(dest_addr, &val[..size_count])?;
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                dest_addr = dest_addr.wrapping_add(size_count as i64);
                                flags &= !Flags::MOV_FLAGS;
                                flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                                count = count.wrapping_sub(1);
                            }
                            Ok(())
                        }
                        Some(CleverOpcode::Repbc) => {
                            let mut val = [0u8; 8];
                            let size_count = 1 << ss;
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            self.write_bytes(dest_addr, &val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val[..size_count],
                                )?;
                                self.write_bytes(dest_addr, &val[..size_count])?;
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                dest_addr = dest_addr.wrapping_add(size_count as i64);
                                flags &= !Flags::MOV_FLAGS;
                                flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                                count = count.wrapping_sub(1);
                            }
                            Ok(())
                        }
                        _ => {
                            let mut val = [0u8; 8];
                            let size_count = 1 << ss;
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            self.write_bytes(dest_addr, &val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            Ok(())
                        }
                    }
                })();
                // If an exception occurs after some operations, update the registers anyways
                self.regs.flags = flags;
                self.regs.gprs[1] = count;
                self.regs.gprs[4] = src_addr as u64;
                self.regs.gprs[5] = dest_addr as u64;
                res?;
            }
            CleverOpcode::Bsto { ss } => {
                let mut src = self.regs.gprs[0];
                let val = src.to_le_bytes();
                let mut dest_addr = self.regs.gprs[5] as i64;
                let mut count = self.regs.gprs[1];
                let mut flags = self.regs.flags;
                let res = (|| -> CPUResult<()> {
                    match insn.prefix() {
                        Some(CleverOpcode::Repbi { cc }) => {
                            let size_count = 1 << ss;
                            if !self.test_cc(cc, flags) {
                                return Ok(());
                            }
                            self.write_bytes(dest_addr, &val[..size_count])?;
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                if !self.test_cc(cc, flags) {
                                    return Ok(());
                                }
                                self.write_bytes(dest_addr, &val[..size_count])?;
                                dest_addr = dest_addr.wrapping_add(size_count as i64);
                                flags &= !Flags::MOV_FLAGS;
                                flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                                count = count.wrapping_sub(1);
                            }
                            Ok(())
                        }
                        Some(CleverOpcode::Repbc) => {
                            let size_count = 1 << ss;
                            self.write_bytes(dest_addr, &val[..size_count])?;
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                self.write_bytes(dest_addr, &val[..size_count])?;
                                dest_addr = dest_addr.wrapping_add(size_count as i64);
                                flags &= !Flags::MOV_FLAGS;
                                flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                                count = count.wrapping_sub(1);
                            }
                            Ok(())
                        }
                        _ => {
                            let size_count = 1 << ss;
                            self.write_bytes(dest_addr, &val[..size_count])?;
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            Ok(())
                        }
                    }
                })();
                // If an exception occurs after some operations, update the registers anyways
                self.regs.flags = flags;
                self.regs.gprs[1] = count;
                self.regs.gprs[5] = dest_addr as u64;
                res?;
            }
            CleverOpcode::Bsca { ss } => {
                let mut val = [0u8; 8];
                let mut src_addr = self.regs.gprs[4] as i64;
                let mut count = self.regs.gprs[1];
                let mut flags = self.regs.flags;
                let res = (|| -> CPUResult<bool> {
                    match insn.prefix() {
                        Some(CleverOpcode::Repbi { cc }) => {
                            let size_count = 1 << ss;
                            if !self.test_cc(cc, flags) {
                                return Ok(false);
                            }
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                if !self.test_cc(cc, flags) {
                                    return Ok(true);
                                }
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val[..size_count],
                                )?;
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                flags &= !Flags::MOV_FLAGS;
                                flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                                count = count.wrapping_sub(1);
                            }
                            Ok(true)
                        }
                        Some(CleverOpcode::Repbc) => {
                            let size_count = 1 << ss;
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val[..size_count],
                                )?;
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                flags &= !Flags::MOV_FLAGS;
                                flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                                count = count.wrapping_sub(1);
                            }
                            Ok(true)
                        }
                        _ => {
                            let size_count = 1 << ss;
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val), ss);
                            Ok(true)
                        }
                    }
                })();
                // If an exception occurs after some operations, update the registers anyways
                self.regs.flags = flags;
                self.regs.gprs[1] = count;
                self.regs.gprs[4] = src_addr as u64;
                if res? {
                    self.regs.gprs[0] = u64::from_le_bytes(val);
                }
            }
            CleverOpcode::Bcmp { ss } => {
                let mut dest_addr = self.regs.gprs[5] as i64;
                let mut src_addr = self.regs.gprs[4] as i64;
                let mut count = self.regs.gprs[1];
                let mut flags = self.regs.flags;
                let size_count = 1 << ss;
                let mut val1 = [0u8; 8];
                let mut val2 = [0u8; 8];
                let res = (|| -> CPUResult<bool> {
                    match insn.prefix() {
                        Some(CleverOpcode::Repbi { cc }) => {
                            if !self.test_cc(cc, flags) {
                                return Ok(false);
                            }
                            self.read_bytes(
                                dest_addr,
                                AccessKind::Access,
                                &mut val1[..size_count],
                            )?;
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            self.read_bytes(src_addr, AccessKind::Access, &mut val2[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            let (_, res_flags) = do_arith_logic(
                                u64::from_le_bytes(val1),
                                u64::from_le_bytes(val2),
                                ss,
                                u64::overflowing_sub,
                            );
                            flags &= !Flags::ARITH_FLAGS;
                            flags |= res_flags;
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                if !self.test_cc(cc, flags) {
                                    return Ok(true);
                                }
                                self.read_bytes(
                                    dest_addr,
                                    AccessKind::Access,
                                    &mut val1[..size_count],
                                )?;
                                dest_addr = dest_addr.wrapping_add(size_count as i64);
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val2[..size_count],
                                )?;
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                let (_, res_flags) = do_arith_logic(
                                    u64::from_le_bytes(val1),
                                    u64::from_le_bytes(val2),
                                    ss,
                                    u64::overflowing_sub,
                                );
                                flags &= !Flags::ARITH_FLAGS;
                                flags |= res_flags;
                                count = count.wrapping_sub(1);
                            }
                            Ok(true)
                        }
                        Some(CleverOpcode::Repbc) => {
                            self.read_bytes(
                                dest_addr,
                                AccessKind::Access,
                                &mut val1[..size_count],
                            )?;
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            self.read_bytes(src_addr, AccessKind::Access, &mut val2[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            let (_, res_flags) = do_arith_logic(
                                u64::from_le_bytes(val1),
                                u64::from_le_bytes(val2),
                                ss,
                                u64::overflowing_sub,
                            );
                            flags &= !Flags::ARITH_FLAGS;
                            flags |= res_flags;
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                self.read_bytes(
                                    dest_addr,
                                    AccessKind::Access,
                                    &mut val1[..size_count],
                                )?;
                                dest_addr = dest_addr.wrapping_add(size_count as i64);
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val2[..size_count],
                                )?;
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                let (_, res_flags) = do_arith_logic(
                                    u64::from_le_bytes(val1),
                                    u64::from_le_bytes(val2),
                                    ss,
                                    u64::overflowing_sub,
                                );
                                flags &= !Flags::ARITH_FLAGS;
                                flags |= res_flags;
                                count = count.wrapping_sub(1);
                            }
                            Ok(true)
                        }
                        _ => {
                            self.read_bytes(
                                dest_addr,
                                AccessKind::Access,
                                &mut val1[..size_count],
                            )?;
                            dest_addr = dest_addr.wrapping_add(size_count as i64);
                            self.read_bytes(src_addr, AccessKind::Access, &mut val2[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            let (_, res_flags) = do_arith_logic(
                                u64::from_le_bytes(val1),
                                u64::from_le_bytes(val2),
                                ss,
                                u64::overflowing_sub,
                            );
                            flags &= !Flags::ARITH_FLAGS;
                            flags |= res_flags;
                            Ok(true)
                        }
                    }
                })();
                // If an exception occurs after some operations, update the registers anyways
                self.regs.flags = flags;
                self.regs.gprs[1] = count;
                self.regs.gprs[5] = dest_addr as u64;
                res?;
            }
            CleverOpcode::Btst { ss } => {
                let test = self.regs.gprs[0];
                let mut val = [0u8; 8];
                let mut src_addr = self.regs.gprs[4] as i64;
                let mut count = self.regs.gprs[1];
                let mut flags = self.regs.flags;
                let res = (|| -> CPUResult<bool> {
                    match insn.prefix() {
                        Some(CleverOpcode::Repbi { cc }) => {
                            let size_count = 1 << ss;
                            if !self.test_cc(cc, flags) {
                                return Ok(false);
                            }
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val) & test, ss);
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                if !self.test_cc(cc, flags) {
                                    return Ok(true);
                                }
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val[..size_count],
                                )?;
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                flags &= !Flags::MOV_FLAGS;
                                flags |= compute_flags_from_val(u64::from_le_bytes(val) & test, ss);
                                count = count.wrapping_sub(1);
                            }
                            Ok(true)
                        }
                        Some(CleverOpcode::Repbc) => {
                            let size_count = 1 << ss;
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val) & test, ss);
                            count = count.wrapping_sub(1);
                            while count > 0 {
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val[..size_count],
                                )?;
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                flags &= !Flags::MOV_FLAGS;
                                flags |= compute_flags_from_val(u64::from_le_bytes(val) & test, ss);
                                count = count.wrapping_sub(1);
                            }
                            Ok(true)
                        }
                        _ => {
                            let size_count = 1 << ss;
                            self.read_bytes(src_addr, AccessKind::Access, &mut val[..size_count])?;
                            src_addr = src_addr.wrapping_add(size_count as i64);
                            flags &= !Flags::MOV_FLAGS;
                            flags |= compute_flags_from_val(u64::from_le_bytes(val) & test, ss);
                            Ok(true)
                        }
                    }
                })();
                // If an exception occurs after some operations, update the registers anyways
                self.regs.flags = flags;
                self.regs.gprs[1] = count;
                self.regs.gprs[4] = src_addr as u64;
                res?;
            }
            op if op.is_cbranch() => {
                let addr = match &insn.operands()[0] {
                    CleverOperand::Immediate(CleverImmediate::Long(_, val)) => *val as i64,
                    CleverOperand::Immediate(CleverImmediate::LongRel(_, disp)) => {
                        *disp + self.regs.ip
                    }
                    _ => unreachable!(),
                };
                if self.test_cc(op.branch_condition().unwrap(), self.regs.flags) {
                    if (addr & 0x1) != 0 {
                        return Err(CPUException::ExecutionAlignment(addr));
                    }

                    self.icache.borrow_mut().clear();
                    self.regs.ip = addr;
                }
            }
            CleverOpcode::JmpA { .. } | CleverOpcode::JmpR { .. } => {
                let addr = match &insn.operands()[0] {
                    CleverOperand::Immediate(CleverImmediate::Long(_, val)) => *val as i64,
                    CleverOperand::Immediate(CleverImmediate::LongRel(_, disp)) => {
                        *disp + self.regs.ip
                    }
                    _ => unreachable!(),
                };
                self.icache.borrow_mut().clear();
                self.regs.ip = addr;
            }
            CleverOpcode::Halt => {
                if self.regs.mode.contains(Mode::XM) {
                    return Err(CPUException::SystemProtection(0));
                }
                self.status = Status::Halted;
            }
            CleverOpcode::Out { ss } => {
                if self.regs.mode.contains(Mode::XM) {
                    return Err(CPUException::SystemProtection(0));
                }
                let ioaddr = self.regs.gprs[2];
                let mut port = self.ioports.get_port_for_addr(ioaddr);
                let size_count = 1 << ss;
                if let Some(prefix) = insn.prefix() {
                    let mut src_addr = self.regs.gprs[4] as i64;
                    let mut count = self.regs.gprs[1];
                    let mut val = [0u8; 8];
                    let flags = self.regs.flags;
                    let res = (|| -> CPUResult<()> {
                        match prefix {
                            CleverOpcode::Repbi { cc } => {
                                if !self.test_cc(cc, flags) {
                                    return Ok(());
                                }
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val[..size_count],
                                )?;
                                if let Some(port) = port.as_deref_mut() {
                                    port.write(size_count as u64, u64::from_le_bytes(val));
                                }
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                count = count.wrapping_sub(1);
                                while count > 0 {
                                    self.read_bytes(
                                        src_addr,
                                        AccessKind::Access,
                                        &mut val[..size_count],
                                    )?;
                                    if let Some(port) = port.as_deref_mut() {
                                        port.write(size_count as u64, u64::from_le_bytes(val));
                                    }
                                    src_addr = src_addr.wrapping_add(size_count as i64);
                                    count = count.wrapping_sub(1);
                                }
                                Ok(())
                            }
                            CleverOpcode::Repbc => {
                                self.read_bytes(
                                    src_addr,
                                    AccessKind::Access,
                                    &mut val[..size_count],
                                )?;
                                if let Some(port) = port.as_deref_mut() {
                                    port.write(size_count as u64, u64::from_le_bytes(val));
                                }
                                src_addr = src_addr.wrapping_add(size_count as i64);
                                count = count.wrapping_sub(1);
                                while count > 0 {
                                    self.read_bytes(
                                        src_addr,
                                        AccessKind::Access,
                                        &mut val[..size_count],
                                    )?;
                                    if let Some(port) = port.as_deref_mut() {
                                        port.write(size_count as u64, u64::from_le_bytes(val));
                                    }
                                    src_addr = src_addr.wrapping_add(size_count as i64);
                                    count = count.wrapping_sub(1);
                                }
                                Ok(())
                            }
                            _ => Err(CPUException::Undefined),
                        }
                    })();
                    self.regs.gprs[4] = src_addr as u64;
                    self.regs.gprs[1] = count;
                    res?;
                } else {
                    let val = self.regs.gprs[0];
                    if let Some(port) = port.as_deref_mut() {
                        port.write(size_count as u64, val);
                    }
                }
            }
            _ => return Err(CPUException::Undefined),
        }

        Ok(())
    }

    pub fn status(&self) -> Status {
        self.status
    }
}

pub struct Processor<'a> {
    mem: Arc<MemoryBus>,
    cpu: CPU,
    io: IOBus,
    init_mem: &'a [u8],
}

mod cpuinfo {
    // 502b9846-d785-11ec-9d64-0242ac120002
    pub const CPUID0: u64 = 0x9d640242ac120002;
    pub const CPUID1: u64 = 0x502b9846d78511ec;

    const CPUEX2V: u64 = 0x0000000000000001;
    const CPUEX2VAS: u64 = 0x0000000000000010;
    const CPUEX2PAS: u64 = 0x0000000000000000;
    #[cfg(feature = "float")]
    const CPUEX2FP: u64 = 0x000000000000000200;
    #[cfg(not(feature = "float"))]
    const CPUEX2FP: u64 = 0x000000000000000000;

    #[cfg(feature = "vector")]
    const CPUEX2VEC: u64 = 0x000000000000001000;

    #[cfg(not(feature = "vector"))]
    const CPUEX2VEC: u64 = 0x000000000000000000;

    #[cfg(feature = "float-ext")]
    const CPUEX2FLOAT_EXT: u64 = 0x000000000000004000;

    #[cfg(not(feature = "float-ext"))]
    const CPUEX2FLOAT_EXT: u64 = 0x000000000000000000;

    #[cfg(feature = "rand")]
    const CPUEX2RAND: u64 = 0x000000000000000100;

    #[cfg(not(feature = "rand"))]
    const CPUEX2RAND: u64 = 0x000000000000000000;

    pub const CPUEX2: u64 =
        CPUEX2V | CPUEX2PAS | CPUEX2VAS | CPUEX2FP | CPUEX2VEC | CPUEX2FLOAT_EXT | CPUEX2RAND;

    pub const MSCPUEX: u64 = 0;

    pub const CPUINFO: [u64; 8] = [CPUID0, CPUID1, CPUEX2, 0, 0, 0, 0, MSCPUEX];
}

impl<'a> Processor<'a> {
    pub fn load_memory(init_mem: &'a [u8], io: IOBus) -> Self {
        let mut bus = MemoryBus::new();
        bus.get_mut().write_bytes(init_mem, 0).unwrap();

        let mem = Arc::new(bus);
        let mut cpu = CPU::new(mem.clone(), io.clone());
        cpu.get_regs_mut().ip = 0xff00;
        cpu.get_regs_mut().flags = Flags::empty();
        cpu.get_regs_mut().mode = Mode::empty();
        cpu.get_regs_mut().cr[0] = 0;
        cpu.get_regs_mut().cpuinfo = cpuinfo::CPUINFO;
        cpu.get_regs_mut().fpcw = 4 | (1 << 4) | (0x1f << 16) | (1 << 24);

        Self {
            cpu,
            mem,
            io,
            init_mem,
        }
    }
}

impl Processor<'_> {
    pub fn dump_state(&self, w: &mut core::fmt::Formatter) -> core::fmt::Result {
        w.write_str("CPU0:\n\n")?;
        w.write_str("Registers:\n")?;
        for i in 0..256 {
            if (i & 0x7) == 0 {
                w.write_fmt(format_args!("{:>3}: ", i))?;
            }
            w.write_fmt(format_args!("{:016X}", self.cpu.get_regs()[i]))?;
            if (i & 0x7) == 0x7 {
                w.write_str("\n")?;
            } else {
                w.write_str(" ")?;
            }
        }

        Ok(())
    }

    pub fn cpu0(&self) -> &CPU {
        &self.cpu
    }

    pub fn cpus(&self) -> &[CPU] {
        core::slice::from_ref(&self.cpu)
    }

    pub fn step_processors<F: FnOnce(&Processor)>(&mut self, reset_cb: F) {
        let res = match self.cpu.status() {
            Status::Enabled => {
                self.cpu.status = Status::Active;
                Ok(())
            }
            Status::Active | Status::Interrupted => self.cpu.step(),
            Status::Halted => self.cpu.poll_exceptions(),
        };

        match res {
            Ok(()) => {}
            Err(CPUException::Reset) => {
                reset_cb(self);
                self.mem.with_locked_bus(|f| {
                    let _ = f.write_bytes(self.init_mem, 0);
                });
                self.cpu.get_regs_mut().ip = 0xff00;
                self.cpu.get_regs_mut().flags = Flags::empty();
                self.cpu.get_regs_mut().mode = Mode::empty();
                self.cpu.get_regs_mut().cr[0] = 0;
                self.cpu.get_regs_mut().cpuinfo = cpuinfo::CPUINFO;
                self.cpu.get_regs_mut().fpcw = 4 | (1 << 4) | (0x1f << 16) | (1 << 24);
                self.cpu.status = Status::Enabled;
            }
            Err(e) => self.cpu.pending_exceptions.push_back(e),
        }
    }
}
