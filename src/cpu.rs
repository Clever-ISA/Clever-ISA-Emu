use std::collections::VecDeque;

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

    pub fn read_bytes(
        &mut self,
        mut out: &mut [u8],
        mut vaddr: i64,
        acc: AccessKind,
    ) -> CPUResult<()> {
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

    pub fn read<T: Pod>(&mut self, vaddr: i64, acc: AccessKind) -> CPUResult<T> {
        let mut val = Zeroable::zeroed();
        self.read_bytes(bytemuck::bytes_of_mut(&mut val), vaddr, acc)?;
        Ok(val)
    }

    pub fn tick(&mut self) -> CPUResult<()> {
        if !self.pending_exceptions.is_empty() && self.status != Status::Interrupted {
            let except = self.pending_exceptions.pop_front().unwrap();
            self.service_exception(except)
        } else {
            let opcode = self.read::<u16>(self.regs.ip, AccessKind::Execute)?;
            let h = opcode & 0xf;

            match opcode {
                _ => Err(CPUException::Undefined),
            }
        }
    }
}
