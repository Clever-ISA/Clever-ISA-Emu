#![feature(cfg_target_has_atomic, strict_provenance)]
#![feature(bigint_helper_methods, const_bigint_helper_methods)]
#![feature(unbounded_shifts, const_unbounded_shifts)]

use bytemuck::{AnyBitPattern, NoUninit, Zeroable};

use core::mem::{size_of, ManuallyDrop};

pub mod bitfield;
pub mod primitive;
pub mod sync;

#[cfg(feature = "float")]
pub mod float;

pub const fn const_zeroed_safe<T: Zeroable>() -> T {
    unsafe { core::mem::zeroed() }
}

pub const fn const_transmute_safe<T: NoUninit, U: AnyBitPattern>(x: T) -> U {
    const {
        assert!(
            size_of::<T>() == size_of::<U>(),
            "cannot transmute between differently sized types"
        );
    }
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

/// Returns the size of the type as a `u64`
///
/// ## Notes
/// If we ever have a 128-bit usize, this function will staticaly error if `size_of::<T>()` exceeds the bounds of `u64`
pub const fn size_of_as_u64<T>() -> u64 {
    const {
        let x = core::mem::size_of::<T>();

        if x > (u64::MAX as usize) {
            panic!("Size of a type exceeds u64::MAX (the future is now, thanks to science)")
        }
        x as u64
    }
}

/// Returns the size of the type as an `i64`
///
/// ## Notes
/// This function will staticaly error if `size_of::<T>()` exceeds the bounds of `i64`
pub const fn size_of_as_i64<T>() -> i64 {
    const {
        let x = core::mem::size_of::<T>();

        if x > (i64::MAX as usize) {
            panic!("Size of a type exceeds i64::MAX")
        }
        x as i64
    }
}
