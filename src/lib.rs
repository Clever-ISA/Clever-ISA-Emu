#[cfg(not(target_endian = "little"))]
compile_error!("Clever-ISA EMU only functions on little-endian processors");

pub mod reg;

pub mod error;

pub mod mem;

pub mod cpu;

pub mod page;

#[cfg(feature = "fp")]
pub mod float;
