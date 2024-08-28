
#[cfg(target_pointer_width = "16")]
core::compile_error!("Attempting to emulate a 64-bit CPU on a 16-bit target is not inadvisable.");

pub mod cpu;
pub mod exec;
pub mod interrupt;
pub mod mem;
pub mod page;
pub mod executor;