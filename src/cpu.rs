use std::{cell::RefCell, collections::VecDeque, convert::TryInto, sync::Arc};

use arch_ops::{
    clever::{
        CleverExtension, CleverImmediate, CleverIndex, CleverInstruction, CleverOpcode,
        CleverOperand, CleverOperandKind, CleverRegister,
    },
    traits::{Address, InsnRead},
};
use lru_time_cache::LruCache;

use crate::{
    error::{AccessKind, CPUException, CPUResult, FaultCharacteristics, FaultStatus},
    mem::{MemoryBus, MemoryController},
    page::PageEntry,
    reg::{Mode, RegsRaw},
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
    regs: RegsRaw,
    pcache: RefCell<LruCache<i64, u64>>,
    pending_exceptions: VecDeque<CPUException>,
    status: Status,
    // L1 I-cache
    icache: RefCell<LruCache<i64, [u16; 16]>>,
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

impl CPU {
    pub fn new(mem: Arc<MemoryBus>) -> CPU {
        CPU {
            bus: mem,
            regs: RegsRaw::new(),
            pcache: RefCell::new(LruCache::with_capacity(1024)),
            pending_exceptions: VecDeque::new(),
            status: Status::Enabled,
            icache: RefCell::new(LruCache::with_capacity(1024)),
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

    pub fn read_aligned<T: Pod>(&self, vaddr: i64, access: AccessKind) -> CPUResult<T> {
        self.bus
            .with_unlocked_bus(|bus| self.read_aligned_in(vaddr, access, bus))
    }

    pub fn write<T: Pod>(&self, vaddr: i64, val: T) -> CPUResult<()> {
        self.bus
            .with_locked_bus(|bus| self.write_in(vaddr, bus, val))
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
        if let Some(except) = self.pending_exceptions.pop_front() {
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
                if extent < (index * 32) {
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
                        | CleverOpcode::Btst { .. },
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
                }
                Ok(CleverInstruction::new(opc, ops))
            }
        }
    }

    pub fn step(&mut self) -> CPUResult<()> {
        self.poll_exceptions()?;
        let insn = self.fetch_insn()?;

        Ok(())
    }
}

pub struct Processor {
    mem: Arc<MemoryBus>,
    cpu: CPU,
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

impl Processor {
    pub fn load_memory(init_mem: &[u8]) -> Processor {
        let mut bus = MemoryBus::new();
        bus.get_mut().write_bytes(init_mem, 0).unwrap();

        let mem = Arc::new(bus);
        let mut cpu = CPU::new(mem.clone());
        cpu.get_regs_mut().ip = 0xff00;
        cpu.get_regs_mut().flags = 0;
        cpu.get_regs_mut().cr[0] = 0;
        cpu.get_regs_mut().cpuinfo = cpuinfo::CPUINFO;
        cpu.get_regs_mut().fpcw = 4 | (1 << 4) | (0x1f << 16) | (1 << 24);

        Self { cpu, mem }
    }

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
}
