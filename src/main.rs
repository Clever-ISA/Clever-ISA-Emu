use std::{
    fs::File,
    io::{stdout, Read, Write},
    time::Duration,
};

use clever_isa_emu::{
    cpu::{Processor, Status},
    io::{IOBus, IOPort},
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

fn main() {
    let mut bus = IOBus::new();
    bus.register(StdoutPort);
    let mut mem = Vec::with_capacity(0x10000);
    let mut file = File::open("bios").unwrap();
    file.read_to_end(&mut mem).unwrap();
    let mut proc = Processor::load_memory(&mem, bus);
    println!("{}", DumpRegState(&proc));
    while proc.cpu0().status() != Status::Halted {
        proc.step_processors(|proc| {
            println!("RESET Encountered. Processor State Before RESET:");
            println!("{}", DumpRegState(&proc));
        });
        std::thread::sleep(Duration::from_millis(500));
    }
    println!("{}", DumpRegState(&proc));
}
