use std::{collections::VecDeque, convert::TryInto};

use lru_time_cache::LruCache;

use crate::{
    error::{AccessKind, CPUException, CPUResult, FaultCharacteristics},
    mem::MemoryBus,
    page::PageEntry,
    reg::RegsRaw,
};

use bytemuck::{Pod, Zeroable};

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Status {
    Running,
    Halted,
    Interrupted,
}

pub struct CPU<'a> {
    regs: RegsRaw,
    pcache: LruCache<i64, u64>,
    pending_exceptions: VecDeque<CPUException>,
    bus: &'a MemoryBus,
    status: Status,
}

fn ss_to_mask(ss: u16) -> u64 {
    (2u64.wrapping_shl(8u32.wrapping_shl(ss as u32) - 1)).wrapping_sub(1)
}

fn signex(val: u64, ss: u16) -> u64 {
    let mut val = val as i64;
    let shift = 64 - (8u32.wrapping_shl(ss as u32) - 1);
    val <<= shift;
    val >>= shift;
    val as u64
}

fn flags_bits(x: u64) -> u64 {
    let mut bits = 0;
    if x == 0 {
        bits |= 2
    }
    if x.count_ones() % 2 != 0 {
        bits |= 0x10
    }
    if x & 0x8000000000000000 != 0 {
        bits |= 8
    }
    bits
}

fn execute_binop(val1: u64, val2: u64, ss: u16, f: impl Fn(u64, u64) -> (u64, bool)) -> (u64, u64) {
    let (result, v) = (f)(val1, val2);
    let mut fbits = flags_bits(result);
    fbits |= (v as u64)
        | (result & (1u64.wrapping_shl(8 << (ss as u32)))).wrapping_shr(8 << (ss as u32));
    fbits |= (!(((val1 ^ result) & (1u64.wrapping_shl(8 << (ss as u32) - 1)))
        .wrapping_shr(8 << (ss as u32) - 1)
        ^ (fbits & 1))
        & 1)
        << 2;
    (result, fbits)
}

#[derive(Copy, Clone, Debug)]
pub enum Operand {
    Register {
        r: u16,
        ss: u16,
    },
    IndirectRegister {
        r: u16,
        ss: u16,
        offset: u16,
        scale: u16,
    },
    Immediate {
        val: u64,
        ss: u16,
        pcrel: bool,
        memory_ref: bool,
    },
}

impl Operand {
    pub const fn is_simple(&self) -> bool {
        matches!(
            self,
            Operand::Register { .. }
                | Operand::Immediate {
                    memory_ref: false,
                    ..
                }
        )
    }
    pub const fn is_writable(&self) -> bool {
        matches!(
            self,
            Operand::Register { .. }
                | Operand::IndirectRegister { .. }
                | Operand::Immediate {
                    memory_ref: true,
                    ..
                }
        )
    }

    pub const fn size(&self) -> u16 {
        match self {
            Operand::Register { ss, .. } => *ss,
            Operand::IndirectRegister { ss, .. } => *ss,
            Operand::Immediate { ss, .. } => *ss,
        }
    }
}

impl<'a> CPU<'a> {
    pub fn new(bus: &'a MemoryBus) -> Self {
        CPU {
            regs: Zeroable::zeroed(),
            pcache: LruCache::with_capacity(1024),
            pending_exceptions: VecDeque::new(),
            bus,
            status: Status::Running,
        }
    }

    pub fn get_regs(&self) -> &RegsRaw {
        &self.regs
    }

    pub fn get_regs_mut(&mut self) -> &mut RegsRaw {
        &mut self.regs
    }

    pub fn lookup_paddr(&mut self, vaddr: i64, acc: AccessKind) -> CPUResult<u64> {
        if self.regs.cr[0] & 1 == 0 {
            Ok(vaddr as u64)
        } else {
            let pg = vaddr >> 12;
            let offset_in_page = (vaddr & 0xfff) as u64;
            let ptl = (self.regs.cr[0] >> 3) & 0x7;
            let pg_range = match ptl {
                0 => -0x80000i64..0x80000i64,
                1 => -0x8000000i64..0x8000000i64,
                2 => -0x800000000i64..0x800000000i64,
                3 => -0x80000000000i64..0x80000000000i64,
                4 => -0x8000000000000i64..0x80000000000i64,
                5..=7 => return Err(CPUException::SystemProtection(0)),
                _ => unreachable!(),
            };

            let mut level = match ptl {
                0 | 1 => 3,
                2 => 4,
                3 => 5,
                4 => 6,
                5..=7 => return Err(CPUException::SystemProtection(0)),
                _ => unreachable!(),
            };

            if !pg_range.contains(&vaddr) {
                Err(CPUException::SystemProtection(0))
            } else {
                if let Some(x) = self.pcache.get(&pg) {
                    Ok(*x)
                } else {
                    let mut entry = PageEntry(self.regs.cr[1]);
                    if (entry.0 & 0xfff) != 0 {
                        return Err(CPUException::PageFault(
                            vaddr,
                            FaultCharacteristics {
                                pref: entry.value() as i64,
                                flevel: level,
                                access_kind: acc,
                                ..Zeroable::zeroed()
                            },
                        ));
                    } else {
                        let mut pg = (pg as u64) & (1u64 << (20 + 8 * ptl) - 1);
                        while level > 0 {
                            let off = (pg & 0x1ff) * 8;
                            pg >>= 9;
                            level -= 1;

                            entry = self
                                .bus
                                .with_unlocked_bus(|c| c.read(entry.value() + off))?;
                            entry.check_access(acc, level, vaddr)?;
                        }

                        let paddr = entry.value() + offset_in_page;
                        self.pcache.insert(vaddr, paddr);
                        Ok(paddr)
                    }
                }
            }
        }
    }

    pub fn status(&self) -> Status {
        self.status
    }

    pub fn service_exception(&mut self, _exception: CPUException) -> CPUResult<()> {
        Ok(())
    }

    pub fn fetch_operand(&mut self) -> CPUResult<Operand> {
        let val = self.read::<u16>(self.regs.ip, AccessKind::Execute)?;

        let (ret, ip) = match val >> 14 {
            0b00 => {
                if val & 0b001110011000000 != 0 {
                    return Err(CPUException::Undefined);
                }

                let ss = (val >> 8) & 0b11;
                Ok((
                    Operand::Register {
                        r: val & 0b111111,
                        ss,
                    },
                    2,
                ))
            }
            0b01 => {
                let r = val & 0b1111;
                let ss = (val & 0b110000) >> 4;
                let k = val & 0b10000 != 0;
                let offset = (val & 0b0011111110000000) >> (7 + 3 * (k as u32));
                let scale = 1u16 << ((val & 0b1110000000 & (-(k as i16) as u16)) >> 7);
                Ok((
                    Operand::IndirectRegister {
                        r,
                        ss,
                        offset,
                        scale,
                    },
                    2,
                ))
            }
            0b10 => {
                if val & 0b0010000000000000 != 0 {
                    return Err(CPUException::Undefined);
                }

                let pcrel = val & 0b0001000000000000 != 0;
                let val = val & ((1 << 12) - 1);
                Ok((
                    Operand::Immediate {
                        val: val as u64,
                        pcrel,
                        memory_ref: false,
                        ss: 3,
                    },
                    2,
                ))
            }
            0b11 => {
                if val & 0b0001100011111111 != 0 {
                    return Err(CPUException::Undefined);
                }
                let pcrel = val & 0b0000010000000000 != 0;
                let memory_ref = val & 0b0010000000000000 != 0;
                let ss = ((val & 0b0000001100000000) >> 8) + 1;
                if ss == 4 {
                    return Err(CPUException::Undefined);
                }
                let mut val = [0u8; 8];
                self.read_bytes(&mut val[..(1 << ss)], self.regs.ip + 2, AccessKind::Execute)?;
                Ok((
                    Operand::Immediate {
                        val: u64::from_le_bytes(val),
                        ss,
                        pcrel,
                        memory_ref,
                    },
                    2 + 1 << (ss as u32),
                ))
            }
            _ => unreachable!(),
        }?;
        self.regs.ip = ip;
        Ok(ret)
    }

    pub fn read_operand(&mut self, op: Operand) -> CPUResult<u64> {
        Ok(match op {
            Operand::Register { r, ss } => {
                if (self.regs.flags & 0x40000) != 0 && (32..63).contains(&r) {
                    return Err(CPUException::SystemProtection(0));
                }
                *self.regs.get_if_valid(r)? & ss_to_mask(ss)
            }
            Operand::IndirectRegister {
                r,
                ss,
                offset,
                scale,
            } => {
                let addr = self.regs[r] as i64 + (offset * scale) as i64;
                let mut buf = [0u8; 8];
                self.read_bytes(&mut buf[..(1 << (ss as u32))], addr, AccessKind::Access)?;
                u64::from_le_bytes(buf)
            }
            Operand::Immediate {
                mut val,
                ss,
                pcrel,
                memory_ref,
            } => {
                if pcrel {
                    val = (self::signex(val, ss) as i64 + self.regs.ip) as u64;
                }

                if memory_ref {
                    let mut buf = [0u8; 8];
                    self.read_bytes(
                        &mut buf[..(1 << (ss as u32))],
                        val as i64,
                        AccessKind::Access,
                    )?;
                    u64::from_le_bytes(buf)
                } else {
                    val
                }
            }
        })
    }

    pub fn write_operand(&mut self, val: u64, op: Operand) -> CPUResult<()> {
        Ok(match op {
            Operand::Register { r, ss } => {
                if (self.regs.flags & 0x40000) != 0 && (32..63).contains(&r) {
                    return Err(CPUException::SystemProtection(0));
                } else if let 16 | 17 = r {
                    return Err(CPUException::Undefined);
                }

                *self.regs.get_mut_if_valid(r)? = val & ss_to_mask(ss);
            }
            Operand::IndirectRegister {
                r,
                ss: _ss,
                offset,
                scale,
            } => {
                let buf = val.to_le_bytes();
                let addr = self.regs[r] as i64 + (offset * scale) as i64;
                self.write_bytes(&buf, addr, AccessKind::Write)?;
            }
            Operand::Immediate {
                val: mut addr,
                ss,
                pcrel,
                memory_ref,
            } => {
                if !memory_ref {
                    return Err(CPUException::Undefined);
                }

                if pcrel {
                    addr = signex(addr, ss) + (self.regs.ip as u64);
                }

                let buf = val.to_le_bytes();
                self.write_bytes(&buf, addr as i64, AccessKind::Write)?;
            }
        })
    }

    pub fn get_operand_addr(&mut self, op: Operand) -> CPUResult<i64> {
        match op {
            Operand::IndirectRegister {
                r,
                ss: _,
                scale,
                offset,
            } => {
                let val = self.regs[r] as i64;
                Ok(val + (offset as i64 * scale as i64))
            }
            Operand::Immediate {
                val,
                ss,
                pcrel,
                memory_ref: true,
            } => {
                if pcrel {
                    Ok(self.regs.ip + (signex(val, ss) as i64))
                } else {
                    Ok((val & ss_to_mask(ss)) as i64)
                }
            }
            _ => Err(CPUException::Undefined),
        }
    }

    pub fn read_bytes(
        &mut self,
        mut out: &mut [u8],
        mut vaddr: i64,
        acc: AccessKind,
    ) -> CPUResult<()> {
        if self.regs.cr[0] & 1 == 0 {
            self.bus
                .with_unlocked_bus(|c| c.read_bytes(out, vaddr as u64))
        } else {
            while !out.is_empty() {
                let paddr = self.lookup_paddr(vaddr, acc)?;
                let mlen = (0x1000 - paddr & 0xfff) as usize;

                if out.len() < mlen {
                    self.bus.with_unlocked_bus(|c| c.read_bytes(out, paddr))?;
                    out = &mut [];
                } else {
                    let (out1, out2) = out.split_at_mut(mlen);
                    self.bus.with_unlocked_bus(|c| c.read_bytes(out1, paddr))?;
                    out = out2;
                    vaddr += mlen as i64;
                }
            }
            Ok(())
        }
    }

    pub fn read<T: Pod>(&mut self, vaddr: i64, acc: AccessKind) -> CPUResult<T> {
        let mut val = Zeroable::zeroed();
        self.read_bytes(bytemuck::bytes_of_mut(&mut val), vaddr, acc)?;
        Ok(val)
    }

    pub fn write_bytes(
        &mut self,
        mut buf: &[u8],
        mut vaddr: i64,
        acc: AccessKind,
    ) -> CPUResult<()> {
        if self.regs.cr[0] & 1 == 0 {
            self.bus
                .with_locked_bus(|c| c.write_bytes(buf, vaddr as u64))
        } else {
            while !buf.is_empty() {
                let paddr = self.lookup_paddr(vaddr, acc)?;
                let mlen = (0x1000 - paddr & 0xfff) as usize;

                if buf.len() < mlen {
                    self.bus.with_locked_bus(|c| c.write_bytes(buf, paddr))?;
                    buf = &[];
                } else {
                    let (out1, out2) = buf.split_at(mlen);
                    self.bus.with_locked_bus(|c| c.write_bytes(out1, paddr))?;
                    buf = out2;
                    vaddr += mlen as i64;
                }
            }
            Ok(())
        }
    }

    pub fn write<T: Pod>(&mut self, value: T, vaddr: i64, acc: AccessKind) -> CPUResult<()> {
        self.write_bytes(bytemuck::bytes_of(&value), vaddr, acc)
    }

    pub fn tick(&mut self) -> CPUResult<()> {
        if !self.pending_exceptions.is_empty() && self.status != Status::Interrupted {
            let except = self.pending_exceptions.pop_front().unwrap();
            self.service_exception(except)
        } else {
            let opcode = self.read::<u16>(self.regs.ip, AccessKind::Execute)?;
            let h = opcode & 0xf;

            match opcode >> 4 {
                0x001 => {
                    let op1 = self.fetch_operand()?;
                    let op2 = self.fetch_operand()?;
                    if !op1.is_simple() && !op2.is_simple() {
                        return Err(CPUException::Undefined);
                    }
                    let val1 = self.read_operand(op1)?;
                    let val2 = self.read_operand(op2)?;
                    if h & 0b1110 != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let (res, flags) = execute_binop(
                        val1,
                        val2,
                        op1.size().max(op2.size()),
                        <u64>::overflowing_add,
                    );
                    self.write_operand(res, op1)?;
                    if h & 0b0001 != 0 {
                        self.regs.flags = self.regs.flags & !0b11111 | flags;
                    }
                    Ok(())
                }
                0x002 => {
                    let op1 = self.fetch_operand()?;
                    let op2 = self.fetch_operand()?;
                    if !op1.is_simple() && !op2.is_simple() {
                        return Err(CPUException::Undefined);
                    }
                    let val1 = self.read_operand(op1)?;
                    let val2 = self.read_operand(op2)?;
                    if h & 0b1110 != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let (res, flags) = execute_binop(
                        val1,
                        val2,
                        op1.size().max(op2.size()),
                        <u64>::overflowing_sub,
                    );
                    self.write_operand(res, op1)?;
                    if h & 0b0001 != 0 {
                        self.regs.flags = self.regs.flags & !0b11111 | flags;
                    }
                    Ok(())
                }
                0x003 => {
                    let op1 = self.fetch_operand()?;
                    let op2 = self.fetch_operand()?;
                    if !op1.is_simple() && !op2.is_simple() {
                        return Err(CPUException::Undefined);
                    }
                    let val1 = self.read_operand(op1)?;
                    let val2 = self.read_operand(op2)?;
                    if h & 0b1110 != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let res = val1 & val2;
                    let flags = flags_bits(res);
                    self.write_operand(res, op1)?;
                    if h & 0b0001 != 0 {
                        self.regs.flags = self.regs.flags & !0b11010 | flags;
                    }
                    Ok(())
                }
                0x004 => {
                    let op1 = self.fetch_operand()?;
                    let op2 = self.fetch_operand()?;
                    if !op1.is_simple() && !op2.is_simple() {
                        return Err(CPUException::Undefined);
                    }
                    let val1 = self.read_operand(op1)?;
                    let val2 = self.read_operand(op2)?;
                    if h & 0b1110 != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let res = val1 | val2;
                    let flags = flags_bits(res);
                    self.write_operand(res, op1)?;
                    if h & 0b0001 != 0 {
                        self.regs.flags = self.regs.flags & !0b11010 | flags;
                    }
                    Ok(())
                }
                0x005 => {
                    let op1 = self.fetch_operand()?;
                    let op2 = self.fetch_operand()?;
                    if !op1.is_simple() && !op2.is_simple() {
                        return Err(CPUException::Undefined);
                    }
                    let val1 = self.read_operand(op1)?;
                    let val2 = self.read_operand(op2)?;
                    if h & 0b1110 != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let res = val1 ^ val2;
                    let flags = flags_bits(res);
                    self.write_operand(res, op1)?;
                    if h & 0b0001 == 0 {
                        self.regs.flags = self.regs.flags & !0b11010 | flags;
                    }
                    Ok(())
                }
                // 0x006 => {
                //     if h & 0b0010 != 0 {
                //         return Err(CPUException::Undefined);
                //     }
                //     let val1 = self.regs[0] as u128;
                //     let val2 = self.regs[3] as u128;
                //     let ss = h >> 2;
                //     let res = val1 * val2;
                //     self.regs[0] = (res as u64) & ss_to_mask(ss);
                //     self.regs[1] = (res >> (1 << (8 << (ss as u32)))) & ss_to_mask(ss);
                //     if h & 0b0001 == 0 {
                //         let p = (res.count_ones() % 2 as u64) << 5;
                //         let c = (res & (ss_to_mask(ss) as u128) != res) as u64;
                //     }
                // }
                0x008 => {
                    if h != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let dst = self.fetch_operand()?;
                    let src = self.fetch_operand()?;
                    if !matches!(dst, Operand::Register { .. })
                        && !matches!(src, Operand::Register { .. })
                    {
                        return Err(CPUException::Undefined);
                    }
                    if !dst.is_writable() {
                        return Err(CPUException::Undefined);
                    }

                    let val = self.read_operand(src)?;
                    self.regs.flags = self.regs.flags & !0b11010 | flags_bits(val);
                    self.write_operand(val, dst)
                }
                0x009 => {
                    if h != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let dst = self.fetch_operand()?;
                    let src = self.fetch_operand()?;
                    if !dst.is_writable() || !matches!(dst, Operand::Register { .. }) {
                        return Err(CPUException::Undefined);
                    }

                    let val = self.get_operand_addr(src)?;
                    self.write_operand(val as u64, dst)
                }
                0x00a => {
                    let r = h;
                    let src = self.fetch_operand()?;
                    let val = self.get_operand_addr(src)? as u64;
                    self.regs.flags = self.regs.flags & !0b11010 | flags_bits(val);
                    self.regs[r] = val;
                    Ok(())
                }
                0x00b => {
                    let r = h;
                    let dst = self.fetch_operand()?;
                    if !dst.is_writable() {
                        return Err(CPUException::Undefined);
                    }
                    let val = self.regs[r];
                    self.regs.flags = self.regs.flags & !0b11010 | flags_bits(val);
                    self.write_operand(val, dst)
                }
                0x014 => {
                    if h != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let src = self.fetch_operand()?;
                    let val = self.read_operand(src)?;
                    let stack = self.regs.gprs[7] - 8;
                    self.regs.gprs[7] -= 8;
                    self.write(val, stack as i64, AccessKind::Write)
                }
                0x015 => {
                    if h != 0 {
                        return Err(CPUException::Undefined);
                    }
                    let dst = self.fetch_operand()?;
                    if !dst.is_writable() || dst.size() != 8 {
                        return Err(CPUException::Undefined);
                    }

                    let stack = self.regs.gprs[7];
                    self.regs.gprs[7] += 8;
                    let val = self.read::<u64>(stack as i64, AccessKind::Access)?;
                    self.write_operand(val, dst)
                }
                0x0016 => {
                    let r = h;
                    let stack = self.regs.gprs[7] - 8;
                    self.regs.gprs[7] -= 8;
                    self.write(self.regs[r], stack as i64, AccessKind::Write)
                }
                0x017 => {
                    let r = h;
                    let stack = self.regs.gprs[7];
                    self.regs.gprs[7] += 8;
                    self.regs[r] = self.read::<u64>(stack as i64, AccessKind::Access)?;
                    Ok(())
                }
                0x018 => {
                    let dst = self.fetch_operand()?;
                    let addr = self.get_operand_addr(dst)?;
                    let gprs = self.regs.gprs;
                    self.write(gprs, addr, AccessKind::Write)
                }
                0x019 => {
                    let src = self.fetch_operand()?;
                    let addr = self.get_operand_addr(src)?;
                    let gprs = self.read(addr, AccessKind::Access)?;
                    self.regs.gprs = gprs;
                    Ok(())
                }
                0x01a => {
                    let dst = self.fetch_operand()?;
                    let addr = self.get_operand_addr(dst)?;
                    let regs: [u64; 32] = self.regs.slice(..32).try_into().unwrap();
                    self.write(regs, addr, AccessKind::Write)
                }
                0x01b => {
                    let src = self.fetch_operand()?;
                    let addr = self.get_operand_addr(src)?;
                    let mut regs = self.read::<[u64; 32]>(addr, AccessKind::Access)?;
                    if regs[18..24].ends_with(&[0; 6]) {
                        return Err(CPUException::SystemProtection(0));
                    }

                    #[cfg(not(feature = "fp"))]
                    {
                        if regs[24..].ends_with(&[0; 6]) {
                            return Err(CPUException::SystemProtection(0));
                        }
                    }

                    regs[16] = self.regs[16];
                    self.regs.slice_mut(..32).copy_from_slice(&regs);
                    Ok(())
                }
                _ => Err(CPUException::Undefined),
            }
        }
    }
}
