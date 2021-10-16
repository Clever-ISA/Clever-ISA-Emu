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

pub struct CPUMemoryController{
    bus: Arc<MemoryBus>,
    regs: RegsRaw,
    
}

pub struct Processor {
    mem: Arc<MemoryBus>,
    cpu: CPU,
}

mod cpuinfo {

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

        Processor { mem, cpu }
    }
}
