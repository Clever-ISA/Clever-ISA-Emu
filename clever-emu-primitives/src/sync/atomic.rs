use crate::primitive::*;
use core::sync::atomic::*;

pub use core::sync::atomic::Ordering;

macro_rules! def_atomic_base{
    {
        $(#[$atomic_cfg:meta] $ty_name:ident [$int_ty:ident @ $order:literal: $atomic_base_ty:ty];)*
    } => {
        $(
            #[repr(transparent)]
            #[$atomic_cfg]
            pub struct $ty_name($atomic_base_ty);

            #[$atomic_cfg]
            impl $ty_name{
                pub const fn new(x: $int_ty) -> Self{
                    Self(<$atomic_base_ty>::new(crate::const_transmute_safe(x)))
                }

                pub fn into_inner(self) -> $int_ty{
                    crate::const_transmute_safe(self.0.into_inner())
                }

                pub fn get_mut(&mut self) -> &mut $int_ty{
                    bytemuck::cast_mut(self.0.get_mut())
                }

                pub fn as_ptr(&self) -> *mut $int_ty{
                    self.0.as_ptr().cast()
                }

                #[inline]
                pub fn load(&self, ord: Ordering) -> $int_ty{
                    crate::const_transmute_safe(self.0.load(ord))
                }

                #[inline]
                pub fn store(&self, val: $int_ty, ord: Ordering){
                    self.0.store(crate::const_transmute_safe(val), ord)
                }

                #[inline]
                pub fn compare_exchange(&self, current: $int_ty, new: $int_ty, success_ord: Ordering, fail_ord: Ordering) -> Result<$int_ty, $int_ty>{
                    match self.0.compare_exchange(crate::const_transmute_safe(current), crate::const_transmute_safe(new), success_ord, fail_ord){
                        Ok(val) => Ok(crate::const_transmute_safe(val)),
                        Err(val) => Err(crate::const_transmute_safe(val))
                    }
                }

                #[inline]
                pub fn compare_exchange_weak(&self, current: $int_ty, new: $int_ty, success_ord: Ordering, fail_ord: Ordering) -> Result<$int_ty, $int_ty>{
                    match self.0.compare_exchange_weak(crate::const_transmute_safe(current), crate::const_transmute_safe(new), success_ord, fail_ord){
                        Ok(val) => Ok(crate::const_transmute_safe(val)),
                        Err(val) => Err(crate::const_transmute_safe(val))
                    }
                }

                #[inline]
                pub fn swap(&self, new: $int_ty, ord: Ordering) -> $int_ty{
                    crate::const_transmute_safe(self.0.swap(crate::const_transmute_safe(new), ord))
                }

                #[inline]
                pub fn fetch_update<F: FnMut($int_ty) -> Option<$int_ty>>(&self, set_ord: Ordering, load_ord: Ordering, mut f: F) -> Result<$int_ty, $int_ty>{
                    match self.0.fetch_update(set_ord, load_ord, move |val| f(crate::const_transmute_safe(val)).map(crate::const_transmute_safe)){
                        Ok(val) => Ok(crate::const_transmute_safe(val)),
                        Err(val) => Err(crate::const_transmute_safe(val))
                    }
                }

                #[cfg(target_endian = $order)]
                #[inline]
                pub fn fetch_add(&self, val: $int_ty, ord: Ordering) -> $int_ty{
                    crate::const_transmute_safe(self.0.fetch_add(crate::const_transmute_safe(val), ord))
                }

                #[cfg(not(target_endian = $order))]
                #[inline]
                pub fn fetch_add(&self, val: $int_ty, ord: Ordering) -> $int_ty{
                    self.fetch_update(Ordering::Relaxed, ord, |x| Some(x.wrapping_add(val))).unwrap()
                }

                #[cfg(target_endian = $order)]
                #[inline]
                pub fn fetch_sub(&self, val: $int_ty, ord: Ordering) -> $int_ty{
                    crate::const_transmute_safe(self.0.fetch_sub(crate::const_transmute_safe(val), ord))
                }

                #[cfg(not(target_endian = $order))]
                #[inline]
                pub fn fetch_sub(&self, val: $int_ty, ord: Ordering) -> $int_ty{
                    self.fetch_update(Ordering::Relaxed, ord, |x| Some(x.wrapping_sub(val))).unwrap()
                }

                #[inline]
                pub fn fetch_and(&self, val: $int_ty, ord: Ordering) -> $int_ty{
                    crate::const_transmute_safe(self.0.fetch_and(crate::const_transmute_safe(val), ord))
                }


                #[inline]
                pub fn fetch_or(&self, val: $int_ty, ord: Ordering) -> $int_ty{
                    crate::const_transmute_safe(self.0.fetch_or(crate::const_transmute_safe(val), ord))
                }


                #[inline]
                pub fn fetch_nand(&self, val: $int_ty, ord: Ordering) -> $int_ty{
                    crate::const_transmute_safe(self.0.fetch_nand(crate::const_transmute_safe(val), ord))
                }

                #[inline]
                pub fn fetch_xor(&self, val: $int_ty, ord: Ordering) -> $int_ty{
                    crate::const_transmute_safe(self.0.fetch_xor(crate::const_transmute_safe(val), ord))
                }
            }
        )*
    }
}

def_atomic_base! {
    #[cfg(target_has_atomic = "8")] AtomicLeU8 [LeU8 @ "little": AtomicU8];
    #[cfg(target_has_atomic = "8")] AtomicBeU8 [BeU8 @ "big": AtomicU8];
    #[cfg(target_has_atomic = "16")] AtomicLeU16 [LeU16 @ "little": AtomicU16];
    #[cfg(target_has_atomic = "16")] AtomicBeU16 [BeU16 @ "big": AtomicU16];
    #[cfg(target_has_atomic = "32")] AtomicLeU32 [LeU32 @ "little": AtomicU32];
    #[cfg(target_has_atomic = "32")] AtomicBeU32 [BeU32 @ "big": AtomicU32];
    #[cfg(target_has_atomic = "64")] AtomicLeU64 [LeU64 @ "little": AtomicU64];
    #[cfg(target_has_atomic = "64")] AtomicBeU64 [BeU64 @ "big": AtomicU64];
}
