#[cfg(not(target_endian = "little"))]
compile_error!("Clever-ISA EMU only functions on little-endian processors");

pub mod cpu;

pub mod aci;

pub mod error;

pub mod float;

pub mod io;

pub mod mem;

pub mod reg;

pub mod page;

pub mod primitive;
