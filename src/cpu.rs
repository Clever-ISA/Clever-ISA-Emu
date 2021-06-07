use cached::{Cached, SizedCache};

use crate::error::{AccessKind, CPUException, FaultCharacteristics};

use crate::mem::MemBus;
use crate::page::PageEntry;
use crate::{
    error::CPUResult,
    mem::MemController,
    page::PageFlags,
    reg::{RegsNamed, RegsRaw},
};

use bytemuck::{Pod, Zeroable};

pub mod cpuex2 {
    pub const IS_CLEVER: u64 = 0b1;
    #[cfg(feature = "fp")]
    pub const FP: u64 = 0b10;
    #[cfg(not(feature = "fp"))]
    pub const FP: u64 = 0;
    pub const PAS: u64 = 0 << 2;
    pub const VAS: u64 = 2 << 5;

    #[cfg(feature = "decimal")]
    pub const DECIMAL: u64 = 0x100;

    #[cfg(not(feature = "decimal"))]
    pub const DECIMAL: u64 = 0;
}

const CPUINFO: [u64; 8] = [
    u64::from_le_bytes(*b"CLEVEREM"),
    u64::from_le_bytes(*b"U      \0"),
    cpuex2::IS_CLEVER | cpuex2::FP | cpuex2::PAS | cpuex2::VAS | cpuex2::DECIMAL,
    0,
    0,
    0,
    0,
    0,
];

pub enum State {
    NotStarted,
    Running,
    Interrupted(CPUException),
    Halted,
}

pub struct CPU<'a> {
    mem: &'a MemBus,
    l1: SizedCache<u64, [u8; 32]>,
    icache: SizedCache<u64, [u16; 16]>,
    vaddr_cache: SizedCache<i64, PageEntry>,
    regs: RegsRaw,
    state: State,
}

impl<'a> CPU<'a> {
    pub fn new(mem: &'a MemBus, ip: i64) -> Self {
        Self {
            mem,
            l1: SizedCache::with_size(256),
            icache: SizedCache::with_size(256),
            vaddr_cache: SizedCache::with_size(1024),
            regs: RegsRaw::from_named(RegsNamed {
                ip,
                cpuinfo: CPUINFO,
                ..RegsNamed::zeroed()
            }),
            state: State::NotStarted,
        }
    }

    pub fn prefetch(&mut self, mut paddr: u64) -> CPUResult<()> {
        paddr &= !0x1f;
        if self.l1.cache_get(&paddr).is_none() {
            let bytes = self.mem.read::<[u8; 32]>(paddr)?;
            self.l1.cache_set(paddr, bytes);
        }

        Ok(())
    }

    pub fn prefetch_instruction(&mut self, mut paddr: u64) -> CPUResult<()> {
        paddr &= !0x1f;
        if self.icache.cache_get(&paddr).is_none() {
            let bytes = self.mem.read::<[u16; 16]>(paddr)?;
            self.icache.cache_set(paddr, bytes);
        }
        Ok(())
    }

    pub fn flush(&mut self) {
        self.l1.cache_clear();
        self.icache.cache_clear();
        self.vaddr_cache.cache_clear();
    }

    pub fn lookup_paddr(&mut self, mut vaddr: i64, access: AccessKind) -> CPUResult<u64> {
        if self.regs.cr[0] & 0x01 == 0 {
            Ok(vaddr as u64)
        } else {
            let max_level = if (self.regs.cr[0] >> 3) & 0x7 < 2 {
                3
            } else {
                4
            };
            let range = match (self.regs.cr[0] >> 3) & 0x7 {
                0 => -0x80000000..=0x7fffffff,
                1 => -0x800000000..=0x7ffffffff,
                2 => -0x800000000000..=0x7ffffffffffff,
                _ => return Err(CPUException::SystemProtection(0)),
            };
            if !range.contains(&vaddr) {
                return Err(CPUException::SystemProtection(0));
            }
            vaddr &= 0xffffffffffff;
            let off_in_page = vaddr as u64 & 0xfff;
            let page = vaddr & !0xfff >> 12;
            if let Some(u) = self.vaddr_cache.cache_get(&page) {
                u.check_access(access, 0, vaddr)?;
                Ok(u.get_value() | off_in_page)
            } else {
                let l4e = vaddr >> 39;
                let l3e = (vaddr >> 30) & 0x1ff;
                let l2e = (vaddr >> 21) & 0x1ff;
                let l1e = (vaddr >> 12) & 0x1ff;

                let mut ptab: PageEntry = bytemuck::cast(self.regs.cr[1]);
                if !ptab.get_flags().is_empty() {
                    return Err(CPUException::PageFault(
                        vaddr,
                        FaultCharacteristics {
                            pref: ptab.get_value() as i64,
                            flevel: max_level + 1,
                            access_kind: access,
                            ..FaultCharacteristics::zeroed()
                        },
                    ));
                }

                if max_level == 4 {
                    ptab = self.mem.read(ptab.get_value() + l4e as u64)?;
                }
                if !ptab.get_flags().contains(PageFlags::PRESENT) {
                    return Err(CPUException::PageFault(
                        vaddr,
                        FaultCharacteristics {
                            pref: ptab.get_value() as i64,
                            flevel: max_level + 1,
                            access_kind: access,
                            ..FaultCharacteristics::zeroed()
                        },
                    ));
                }

                ptab = self.mem.read(ptab.get_value() + l3e as u64)?;
                if !ptab.get_flags().contains(PageFlags::PRESENT) {
                    return Err(CPUException::PageFault(
                        vaddr,
                        FaultCharacteristics {
                            pref: ptab.get_value() as i64,
                            flevel: max_level + 1,
                            access_kind: access,
                            ..FaultCharacteristics::zeroed()
                        },
                    ));
                }

                ptab = self.mem.read(ptab.get_value() + l2e as u64)?;
                if !ptab.get_flags().contains(PageFlags::PRESENT) {
                    return Err(CPUException::PageFault(
                        vaddr,
                        FaultCharacteristics {
                            pref: ptab.get_value() as i64,
                            flevel: max_level + 1,
                            access_kind: access,
                            ..FaultCharacteristics::zeroed()
                        },
                    ));
                }
                ptab = self.mem.read(ptab.get_value() + l1e as u64)?;
                ptab.check_access(access, 0, vaddr)?;
                self.vaddr_cache.cache_set(vaddr & !0xfff, ptab);
                Ok(ptab.get_value())
            }
        }
    }

    pub fn read_bytes(&mut self, vaddr: i64, out: &mut [u8]) -> CPUResult<()> {
        // TODO: use l1 cache
        if self.regs.cr[0] & 0x1 == 0 {
            self.mem.read_bytes(vaddr as u64, out)
        } else {
            let off_in_page = (vaddr & 0xfff) as usize;
            let paddr = self.lookup_paddr(vaddr, AccessKind::Access)?;
            if off_in_page + out.len() > 0x1000 {
                let width = 0x1000 - off_in_page;
                self.mem.read_bytes(paddr, &mut out[..width])?;
                self.read_bytes(vaddr + (off_in_page as i64), &mut out[width..])
            } else {
                self.mem.read_bytes(paddr, out)
            }
        }
    }

    pub fn read<T: Pod>(&mut self, vaddr: i64) -> CPUResult<T> {
        let mut val = T::zeroed();

        self.read_bytes(vaddr, bytemuck::bytes_of_mut(&mut val))?;

        Ok(val)
    }

    pub fn write_bytes(&mut self, vaddr: i64, in_bytes: &[u8]) -> CPUResult<()> {
        if self.regs.cr[0] & 0x1 == 0 {
            self.mem.write_bytes(vaddr as u64, in_bytes)
        } else {
            let off_in_page = (vaddr & 0xfff) as usize;
            let paddr = self.lookup_paddr(vaddr, AccessKind::Access)?;
            if off_in_page + in_bytes.len() > 0x1000 {
                let width = 0x1000 - off_in_page;
                self.mem.write_bytes(paddr, &in_bytes[..width])?;
                self.write_bytes(vaddr + (width as i64), &in_bytes[width..])
            } else {
                self.mem.write_bytes(paddr, in_bytes)
            }
        }
    }

    pub fn write<T: Pod>(&mut self, vaddr: i64, val: T) -> CPUResult<()> {
        self.write_bytes(vaddr, bytemuck::bytes_of(&val))
    }

    pub fn tick(&mut self) -> CPUResult<()> {
        let iaddr = self.lookup_paddr(self.regs.ip, AccessKind::Execute)?;
        let opc = self.mem.read::<u16>(iaddr)?;
        let h = opc & 0xf;
        match opc >> 4 {
            0xfc6 => {
                if h != 0 {
                    Err(CPUException::Undefined)
                } else if self.regs[3] == 0 {
                    Err(CPUException::Undefined)
                } else {
                    let stsp = self.regs.gprs[7];
                    let scip = self.regs.cr[3] as i64;
                    let scsp = self.regs.cr[4] as i64;
                    if scip & 1 != 0 {
                        return Err(CPUException::ExecutionAlignment(scip));
                    }
                    let ipaddr = self.lookup_paddr(scip, AccessKind::Access)?;
                    self.prefetch_instruction(ipaddr)?;
                    let spaddr = self.lookup_paddr(scsp, AccessKind::Write)?;
                    self.prefetch(spaddr)?;
                    if scsp != 0 {
                        self.regs.gprs[7] = scsp as u64;
                    }
                    if self.regs.cr[5] & 1 != 0 {
                        self.regs.gprs[14] = stsp;
                        self.regs.gprs[15] = self.regs.ip as u64;
                    } else {
                        self.write((self.regs.gprs[7] - 16) as i64, [stsp, self.regs.ip as u64])?;
                        self.regs.gprs[7] -= 16;
                    }

                    if self.regs.cr[5] & 2 != 0 {
                        self.regs.gprs[13] = self.regs.flags;
                    }
                    self.regs.flags &= !0x400;
                    self.regs.ip = scip;
                    Ok(())
                }
            }

            _ => Err(CPUException::Undefined),
        }
    }
}
