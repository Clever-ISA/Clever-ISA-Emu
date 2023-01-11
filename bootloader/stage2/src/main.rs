#![no_std]
#![no_main]

#[no_mangle]
pub extern "C" fn _start() -> !{

    loop{core::arch::asm!("hlt")}
}