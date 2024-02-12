use core::ffi::c_void;

mod sealed {
    pub trait SealedIoValue {}
}

use sealed::SealedIoValue;

impl SealedIoValue for u8 {}
impl SealedIoValue for u16 {}
impl SealedIoValue for u32 {}
impl SealedIoValue for u64 {}

impl SealedIoValue for i8 {}
impl SealedIoValue for i16 {}
impl SealedIoValue for i32 {}
impl SealedIoValue for i64 {}

pub unsafe trait IoValue: SealedIoValue {}

unsafe impl<T: SealedIoValue> IoValue for T {}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct IoAddr<T>(*mut T);

pub fn io_read<T: IoValue>(addr: IoAddr<T>) -> T {
    let val: u64;
    unsafe {
        clever_asm!("in {size:s}", size = const core::mem::size_of::<T>(), in("r1") addr.0, lateout("r0") val);
    }

    unsafe { core::mem::transmute_copy(&val) }
}

pub fn io_write<T: IoValue>(addr: IoAddr<T>, rval: T) {
    let mut val: u64 = 0u64;
    unsafe {
        core::ptr::addr_of_mut!(val).cast::<T>().write(rval);
    }

    unsafe {
        clever_asm!("out {size:s}", size= const core::mem::size_of::<T>(), in("r1") addr.0, in("r0") val)
    }
}
