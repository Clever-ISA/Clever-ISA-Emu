use std::{cell::RefCell, collections::VecDeque, convert::TryInto, sync::Arc};

use lru_time_cache::LruCache;

use crate::{
    error::{AccessKind, CPUException, CPUResult, FaultCharacteristics},
    mem::{MemoryBus, MemoryController},
    page::PageEntry,
    reg::RegsRaw,
};

use bytemuck::{Pod, Zeroable};

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Status {
    Enabled,
    Active,
    Halted,
    Interrupted,
}

pub struct CPU {
    bus: Arc<MemoryBus>,
    regs: RegsRaw,
    pcache: RefCell<LruCache<i64, u64>>,
    pending_exceptions: VecDeque<CPUException>,
    status: Status,
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

impl CPU {
    pub fn new(mem: Arc<MemoryBus>) -> CPU {
        CPU {
            bus: mem,
            regs: RegsRaw::new(),
            pcache: RefCell::new(LruCache::with_capacity(1024)),
            pending_exceptions: VecDeque::new(),
            status: Status::Enabled,
        }
    }

    fn resolve_vaddr_in(&self, vaddr: i64, bus: &MemoryController) -> CPUResult<u64> {
        if self.regs.cr[0] & 0x01 == 0 {
            return Ok(vaddr as u64);
        }
        if let Some(&x) = self.pcache.borrow_mut().get(&vaddr) {
            Ok(x)
        } else {
            let pagetbl = self.regs.cr[1];

            todo!()
        }
    }

    pub fn resolve_vaddr(&self, vaddr: i64) -> CPUResult<u64> {
        if self.regs.cr[0] & 0x01 == 0 {
            Ok(vaddr as u64)
        } else {
            self.bus
                .with_unlocked_bus(|bus| self.resolve_vaddr_in(vaddr, bus))
        }
    }

    pub fn get_regs_mut(&mut self) -> &mut RegsRaw {
        &mut self.regs
    }

    pub fn get_regs(&self) -> &RegsRaw {
        &self.regs
    }
}

pub struct Processor {
    mem: Arc<MemoryBus>,
    cpu: CPU,
}

mod cpuinfo {
    pub const CPUID0: u64 = 0;
    pub const CPUID1: u64 = 0;

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
