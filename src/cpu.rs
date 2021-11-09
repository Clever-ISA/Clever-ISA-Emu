use std::{collections::VecDeque, convert::TryInto, sync::Arc};

use half::f16;
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
    Enabled,
    Active,
    Halted,
    Interrupted,
}

pub struct CPU {
    regs: RegsRaw,
    pcache: LruCache<i64, u64>,
    bus: Arc<MemoryBus>,
    pending_exceptions: VecDeque<CPUException>,
    status: Status,
}

pub struct CPUMemoryController {
    bus: Arc<MemoryBus>,
    regs: RegsRaw,
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

    pub const CPUEX2: u64 = CPUEX2V | CPUEX2PAS | CPUEX2VAS | CPUEX2FP | CPUEXEC2VEC;

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
        cpu.get_regs_mut().cpuinfo = cpuinfo::CPUINFO
    }
}
