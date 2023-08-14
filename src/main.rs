use std::{
    fs::File,
    io::{stdout, Read, Seek, SeekFrom, Write},
    sync::Arc,
    time::Duration,
};

use bytemuck::{Pod, Zeroable};
use clever_isa_emu::{
    cpu::{Processor, Status},
    io::{IOBus, IOPort},
    mem::MemoryBus,
};

pub struct DumpRegState<'a, 'b>(&'a Processor<'b>);

impl core::fmt::Display for DumpRegState<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.0.dump_state(f)
    }
}

pub struct StdoutPort;

impl IOPort for StdoutPort {
    fn matches_addr(&self, addr: u64) -> bool {
        return addr == 0x100000000;
    }

    fn write(&mut self, size: u64, val: u64) {
        let bytes = val.to_le_bytes();
        stdout()
            .lock()
            .write_all(&bytes[..(size as usize)])
            .unwrap();
    }
}

#[repr(C)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
pub struct DmaReq {
    pub paddr: u64,
    pub len: u64,
    pub diskoff: u64,
    pub flags: u64,
}

pub struct FastDmaStructure<W> {
    backing: W,
    membus: Arc<MemoryBus>,
}

impl<W> FastDmaStructure<W> {
    pub const fn new(backing: W, membus: Arc<MemoryBus>) -> Self {
        Self { backing, membus }
    }

    pub fn into_inner(self) -> W {
        self.backing
    }
}

impl<W: Read + Seek> IOPort for FastDmaStructure<W> {
    fn matches_addr(&self, addr: u64) -> bool {
        addr == 0x100000001
    }

    fn read(&mut self, size: u64) -> u64 {
        1
    }

    fn write(&mut self, size: u64, val: u64) {
        let addr = val;

        let _ = (|| {
            let mut req: DmaReq = self.membus.with_unlocked_bus(|bus| bus.read(addr)).ok()?;

            if req.flags & 1 != 0 {
                None?
            }

            self.backing.seek(SeekFrom::Start(req.diskoff)).ok()?;

            while req.len >= 1024 {
                let mut buf = [0u8; 1024];
                self.backing.read(&mut buf).ok()?;
                self.membus
                    .with_locked_bus(|bus| bus.write_bytes(&buf, req.paddr))
                    .ok()?;

                req.paddr += 1024;
                req.len -= 1024;
            }

            let mut buf = [0u8; 1024];
            self.backing.read(&mut buf[..(req.len as usize)]).ok()?;
            self.membus
                .with_locked_bus(|bus| bus.write_bytes(&buf[..(req.len as usize)], req.paddr))
                .ok()?;

            Some(())
        })();
    }
}

fn main() {
    let mut bus = IOBus::new();
    bus.register(StdoutPort);
    let mut mem = Vec::with_capacity(0x10000);
    let mut file = File::open("bios").unwrap();
    file.read_to_end(&mut mem).unwrap();
    let mut proc = Processor::load_memory(&mem, bus);

    if let Ok(file) = File::open("boot.img") {
        let bus = proc.get_memory().clone();
        proc.get_iobus_mut()
            .register(FastDmaStructure::new(file, bus));
    }

    while proc.cpu0().status() != Status::Halted {
        proc.step_processors(|proc| {
            println!("RESET Encountered. Processor State Before RESET:");
            println!("{}", DumpRegState(&proc));
            println!("Press enter to continue> ");
            let _ = std::io::stdin().read_line(&mut String::new());
        });
        std::thread::sleep(Duration::from_millis(500));
    }
    println!("{}", DumpRegState(&proc));
}
