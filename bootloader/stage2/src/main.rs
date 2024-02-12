#![no_std]
#![no_main]
#![feature(inline_const, strict_provenance)]

#[cfg(target_arch = "clever")]
macro_rules! clever_asm{
    ($($tt:tt)*) => {
        ::core::arch::asm!($($tt)*)
    }
}

#[cfg(not(target_arch = "clever"))]
macro_rules! clever_asm {
    ($($str_lit:literal),* $(,$($operands:tt)*)? ) => {{
        unsafe fn __unsafe() {}

        __unsafe();
        $(clever_asm!(@$($operands)*))?

    }};

    (@in($tt:tt) $val:expr $(, $($rest:tt)*)?) => {{
        let _val = $val;

        $(clever_asm!(@$($rest)*))?
    }};
    (@out($tt:tt) $val:expr $(, $($rest:tt)*)?) =>{{
        $val = unsafe{core::mem::zeroed()};
        $(clever_asm!(@$($rest)*))?
    }};

    (@lateout($tt:tt) $val:expr $(, $($rest:tt)*)?) => {{
        $val = core::mem::zeroed();
        $(clever_asm!(@$($rest)*))?
    }};
    (@ $name:ident =  in($tt:tt) $val:expr $(, $($rest:tt)*)?) => {{
        let _val = $val;

        $(clever_asm!(@$($rest)*))?
    }};
    (@ $name:ident =  out($tt:tt) $val:ident $(, $($rest:tt)*)?) =>{{
        $val = unsafe{core::mem::zeroed()};
        $(clever_asm!(@$($rest)*))?
    }};
    (@ $name:ident = lateout($tt:tt) $val:ident $(, $($rest:tt)*)?) => {{
        $val = unsafe{core::mem::zeroed()};
        $(clever_asm!(@$($rest)*))?
    }};
    (@ $name:ident = const $val:expr $(, $($rest:tt)*)?) => {{
        let _ = const{$val};
        $(clever_asm!(@$($rest)*))?
    }};
    (@ $name:ident = sym $path:path $(, $($rest:tt)*)?) => {{
        let _val = $path;
        $(clever_asm!(@$($rest)*))?
    }};

    (@ options($($opt:ident),*) $(, $($rest:tt)*)?) => {{
        $(clever_asm!(@$($rest)*);)?
        clever_asm!(@@ $($opt),*)
    }};
    (@ clobbers_abi($($abi:literal),*)$(, $($rest:tt)*)?) => {{
        const _: &[&str] = &[$($abi),*];
        $(clever_asm!(@$($rest)*))?
    }};
    (@@) => {{}};

    (@@ noreturn $(,$rest:ident)*) => {{
        clever_asm!(@@ $($rest),*);
        ::core::hint::unreachable_unchecked()
    }
    };

    (@@ pure $(,$rest:ident)*) => {
        clever_asm!(@@ $($rest),*)
    };
    (@@ nomem $(,$rest:ident)*) => {
        clever_asm!(@@ $($rest),*)
    };
    (@@ readonly $(,$rest:ident)*) => {
        clever_asm!(@@ $($rest),*)
    };
    (@@ preserves_flags $(,$rest:ident)*) => {
        clever_asm!(@@ $($rest),*)
    };
    (@@ nostack $(,$rest:ident)*) => {
        clever_asm!(@@ $($rest),*)
    };
}

pub mod aci;
pub mod caps;
pub mod io;

#[no_mangle]
pub extern "C" fn _start() -> ! {
    loop {
        unsafe { clever_asm!("hlt") }
    }
}

#[panic_handler]
fn __panic(_info: &core::panic::PanicInfo) -> ! {
    unsafe { clever_asm!("und", options(noreturn)) }
}
