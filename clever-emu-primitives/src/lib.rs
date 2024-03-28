#![feature(cfg_target_has_atomic, strict_provenance)]

use bytemuck::{AnyBitPattern, NoUninit};

use core::mem::{size_of, ManuallyDrop};

pub mod bitfield;
pub mod primitive;
pub mod sync;

#[cfg(feature = "float")]
pub mod float;

pub const fn const_transmute_safe<T: NoUninit, U: AnyBitPattern>(x: T) -> U {
    assert!(size_of::<T>() == size_of::<U>());
    union Transmuter<T, U> {
        base: ManuallyDrop<T>,
        result: ManuallyDrop<U>,
    }

    unsafe {
        ManuallyDrop::into_inner(
            Transmuter {
                base: ManuallyDrop::new(x),
            }
            .result,
        )
    }
}

/// returns a subslice that is well aligned to `U`.
///
/// Unlike [`slice::align_to`], it is a safe function because [`bytemuck`] says we can transmute between the types soundly
///
pub fn pod_align_to<T: NoUninit, U: AnyBitPattern>(x: &[T]) -> (&[T], &[U], &[T]) {
    unsafe { x.align_to() }
}

/// returns a subslice that is well aligned to `U`.
///
/// Unlike [`slice::align_to`], it is a safe function because [`bytemuck`] says we can transmute between the types soundly
///
pub fn pod_align_to_mut<T: NoUninit + AnyBitPattern, U: NoUninit + AnyBitPattern>(
    x: &mut [T],
) -> (&mut [T], &mut [U], &mut [T]) {
    unsafe { x.align_to_mut() }
}
