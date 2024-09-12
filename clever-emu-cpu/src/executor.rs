#![allow(unexpected_cfgs)] // feature = "multithreading" is not being worked on yet, but I'm leaving the previous code.

use core::num;
use std::{num::NonZero, sync::Arc};

use clever_emu_errors::{CPUException, CPUResult};
use clever_emu_mem::{
    bus::{GlobalMemory, LocalMemory},
    io::IoBus,
};

use crate::cpu::Cpu;
use crate::cpu::CpuMemorySizes;

use clever_emu_mem::{
    cache::CacheLine,
    phys::{Page, SysMemory},
};

#[cfg(feature = "multithreading")]
pub struct SendPtr<T>(*mut T);

#[cfg(feature = "multithreading")]
unsafe impl<T> Send for SendPtr<T> {}

pub struct CpuExecutor {
    #[cfg(not(feature = "multithreading"))]
    cpus: Vec<Cpu>,
    l3cache: Arc<GlobalMemory>,
    iobus: Arc<IoBus>,
    #[cfg(feature = "multithreading")]
    threads: Vec<JoinHandle<()>>,
    #[cfg(feature = "multithreading")]
    force_stop_signal: AtomicBool,

    #[cfg(feature = "multithreading")]
    start_signal: AtomicBool,
    #[cfg(feature = "multithreading")]
    reset_signal: AtomicBool,
    #[cfg(feature = "multithreading")]
    run_lock: Mutex<()>,
}

impl Drop for CpuExecutor {
    fn drop(&mut self) {
        #[cfg(feature = "multithreading")]
        {
            self.force_stop_signal.store(true, Ordering::Release);
            for th in core::mem::take(&mut self.threads) {
                th.thread().unpark(); // In case the thread is parked on waiting for the start_signal
                let _ = th.join();
            }
        }
        // We've synced with our threads, so its safe to `Drop` the `Cpu`s.
    }
}

fn process_exceptions(cpu: &mut Cpu, f: impl FnOnce(&mut Cpu) -> CPUResult<()>) -> CPUResult<()> {
    match f(cpu) {
        Ok(()) => Ok(()),
        Err(CPUException::Reset) => Err(CPUException::Reset),
        Err(e) => match cpu.handle_exception(e) {
            Ok(()) => Ok(()),
            Err(_) if e == CPUException::Abort => Err(CPUException::Reset),
            Err(CPUException::Reset) => Err(CPUException::Reset),
            Err(_) => cpu
                .handle_exception(CPUException::Abort)
                .map_err(|_| CPUException::Reset),
        },
    }
}

impl CpuExecutor {
    #[cfg(not(feature = "multithreading"))]
    pub fn new(
        num_cpus: NonZero<usize>,
        memory_sizes: CpuMemorySizes,
        sys_memory: Arc<SysMemory>,
        iobus: IoBus,
    ) -> Self {
        let l3cache = Arc::new(GlobalMemory::new(
            sys_memory,
            memory_sizes.l3size / (CacheLine::SIZE as usize),
        ));

        let iobus = Arc::new(iobus);

        let cpus = (0..num_cpus.get())
            .map(|_| Cpu::new(l3cache.clone(), iobus.clone(), memory_sizes))
            .collect::<Vec<_>>();
        cpus[0].enable(true);

        Self {
            cpus,
            l3cache,
            iobus,
        }
    }

    pub fn global_memory(&self) -> &GlobalMemory {
        &self.l3cache
    }

    pub fn init(&mut self) {
        for cpu in &mut self.cpus {
            cpu.init();
        }
    }

    pub fn run(&mut self) -> CPUResult<()> {
        loop {
            for cpu in &mut self.cpus {
                process_exceptions(cpu, |cpu| cpu.tick())?;
            }
        }
    }
}
