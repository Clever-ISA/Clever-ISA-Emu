use clever_isa_emu::cpu::Processor;

pub struct DumpRegState<'a>(&'a Processor);

impl core::fmt::Display for DumpRegState<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.0.dump_state(f)
    }
}

fn main() {
    let proc = Processor::load_memory(&[0; 1024]);
    println!("{}", DumpRegState(&proc))
}
