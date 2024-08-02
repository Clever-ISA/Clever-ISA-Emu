#[doc(hidden)]
pub mod __exports {
    pub use bytemuck::{Pod, Zeroable};
    pub use paste::paste;
}

#[macro_export]
macro_rules! bitfield{
    {
        $(#[$meta:meta])*
        $vis:vis struct $bitfield_ty:ident : $base_ty:ty{
            $($(#[$meta2:meta])* $vis2:vis $field_name:ident @ $placement_start:literal $(.. $placement_end:literal)? : $ty:ty ),*
            $(,)?
        }
    } => {

        $(#[$meta])*
        #[derive(Copy, Clone, PartialEq, Eq, Hash, Default, Debug, $crate::bitfield::__exports::Zeroable, $crate::bitfield::__exports::Pod)]
        #[repr(transparent)]
        $vis struct $bitfield_ty($base_ty);

        const _: () = {
            fn test() -> impl $crate::bitfield::BitfieldTy{
                <$base_ty>::default()
            }
        };

        impl $bitfield_ty{

            $vis const fn from_bits(val: $base_ty) -> Self{
                Self(val)
            }

            $vis const fn bits(self) -> $base_ty{
                self.0
            }

            #[allow(unused_mut)]
            #[inline]
            $vis fn validate(self) -> bool{
                let mut field = <$base_ty>::new(0);
                let mut fields_valid = true;

                $($(#[$meta2])*{
                    let placement = $placement_start $(.. $placement_end)?;
                    field = $crate::bitfield::BitfieldPosition::insert(&placement, field, <$base_ty>::new(!0));
                    fields_valid |= $crate::bitfield::FromBitfield::<$base_ty>::validate(self. $field_name ());
                })*

                ((self.bits() & !field) == 0) && fields_valid
            }

            $(
                #[inline]
                $(#[$meta2])*
                $vis2 fn $field_name(&self) -> $ty{
                    let placement = $placement_start $(.. $placement_end)?;
                    let bits = $crate::bitfield::BitfieldPosition::extract(&placement,self.0);

                    $crate::bitfield::FromBitfield::from_bits(bits)
                }

                $crate::bitfield::__exports::paste!{
                    #[inline]
                    $(#[$meta2])*
                    $vis2 fn [<with_ $field_name>](val: $ty) -> Self{

                        let placement = $placement_start $(.. $placement_end)?;

                        let bits = $crate::bitfield::FromBitfield::to_bits(val);

                        Self($crate::bitfield::BitfieldPosition::insert(&placement, $crate::const_zeroed_safe(), bits))
                    }

                    #[inline]
                    $(#[$meta2])*
                    $vis2 fn [<insert_ $field_name>](mut self, val: $ty) -> Self{
                        let placement = $placement_start $(.. $placement_end)?;

                        let bits = $crate::bitfield::FromBitfield::to_bits(val);

                        self.0 = $crate::bitfield::BitfieldPosition::insert(&placement, self.0, bits);
                        self
                    }

                    #[inline]
                    $(#[$meta2])*
                    $vis2 fn [<set_ $field_name>](&mut self, val: $ty){
                        let placement = $placement_start $(.. $placement_end)?;

                        let bits = $crate::bitfield::FromBitfield::to_bits(val);

                        self.0 = $crate::bitfield::BitfieldPosition::insert(&placement, self.0, bits);
                    }
                }
            )*
        }

        impl ::core::ops::BitAnd for $bitfield_ty{
            type Output = Self;
            #[inline]
            fn bitand(self, rhs: Self) -> Self{
                Self(self.0 & rhs.0)
            }
        }

        impl ::core::ops::BitOr for $bitfield_ty{
            type Output = Self;
            #[inline]
            fn bitor(self, rhs: Self) -> Self{
                Self(self.0 | rhs.0)
            }
        }

        impl ::core::ops::BitXor for $bitfield_ty{
            type Output = Self;
            #[inline]
            fn bitxor(self, rhs: Self) -> Self{
                Self(self.0 ^ rhs.0)
            }
        }

        impl ::core::ops::BitAndAssign for $bitfield_ty{
            #[inline]
            fn bitand_assign(&mut self, rhs: Self){
                *self = *self & rhs;
            }
        }

        impl ::core::ops::BitOrAssign for $bitfield_ty{
            #[inline]
            fn bitor_assign(&mut self, rhs: Self){
                *self = *self | rhs;
            }
        }

        impl ::core::ops::BitXorAssign for $bitfield_ty{
            #[inline]
            fn bitxor_assign(&mut self, rhs: Self){
                *self = *self ^ rhs;
            }
        }

        impl ::core::ops::Not for $bitfield_ty{
            type Output = Self;

            #[inline]
            fn not(self) -> Self{
                Self(!self.0)
            }
        }


        impl ::core::fmt::Display for $bitfield_ty{
            #[allow(unused_variables, unused_mut, unused_assignments)]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                let mut sep = "";
                $(
                    {
                        let field = self.$field_name();
                        if $crate::bitfield::DisplayBitfield::present(&field){
                            f.write_str(sep)?;
                            sep = " | ";
                            $crate::bitfield::DisplayBitfield::display(&field, ::core::stringify!($field_name), f)?;
                        }
                    }
                )*

                Ok(())
            }
        }

        impl<T> $crate::bitfield::FromBitfield<T> for $bitfield_ty where T: $crate::bitfield::BitfieldTy,
            $base_ty: $crate::bitfield::FromBitfield<T>{
            fn from_bits(bits: T) -> Self{
                Self::from_bits($crate::bitfield::FromBitfield::<T>::from_bits(bits))
            }
            fn to_bits(self) -> T{
                $crate::bitfield::FromBitfield::<T>::to_bits(self.bits())
            }

            fn validate(self) -> bool{
                self.validate()
            }
        }

        impl $crate::bitfield::DisplayBitfield for $bitfield_ty{
            fn present(&self) -> bool{
                $(({
                    let field = self.$field_name();
                    $crate::bitfield::DisplayBitfield::present(&field)
                }) |)* false
            }
            fn display(&self, name: &str,f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                f.write_fmt(::core::format_args!("{}({})",name,self))
            }
        }
    }
}

use std::{
    marker::PhantomData,
    ops::{BitAnd, BitOr, Not, Range, Shl},
};

pub use bitfield;

mod private {
    pub trait Sealed {}
}

use bytemuck::{Pod, Zeroable};
use private::Sealed;

use crate::primitive::*;

impl Sealed for LeU8 {}
impl Sealed for LeU16 {}
impl Sealed for LeU32 {}
impl Sealed for LeU64 {}
impl Sealed for LeU128 {}
impl Sealed for BeU8 {}
impl Sealed for BeU16 {}
impl Sealed for BeU32 {}
impl Sealed for BeU64 {}
impl Sealed for BeU128 {}
impl Sealed for u32 {}
impl Sealed for Range<u32> {}

pub trait BitfieldTy:
    Sealed
    + Sized
    + Pod
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + Not<Output = Self>
    + Shl<u32, Output = Self>
{
    const ZERO: Self = crate::const_zeroed_safe();
}

impl BitfieldTy for LeU8 {}
impl BitfieldTy for LeU16 {}
impl BitfieldTy for LeU32 {}
impl BitfieldTy for LeU64 {}
impl BitfieldTy for LeU128 {}

impl BitfieldTy for BeU8 {}
impl BitfieldTy for BeU16 {}
impl BitfieldTy for BeU32 {}
impl BitfieldTy for BeU64 {}
impl BitfieldTy for BeU128 {}

pub trait BitfieldPosition<T: BitfieldTy>: Sealed {
    fn extract(&self, bits: T) -> T;
    fn insert(&self, val: T, bits: T) -> T;
}

macro_rules! impl_bitfield_pos{
    ($($tys:ty),*) => {
        $(
            impl BitfieldPosition<$tys> for u32{
                fn extract(&self, bits: $tys)-> $tys{
                    let mask = <$tys>::new(1) << (<$tys>::new(*self as _));

                    (bits & mask) >> (<$tys>::new(*self as _))
                }

                fn insert(&self, val: $tys, bits: $tys) -> $tys{
                    let mask = <$tys>::new(1) << (<$tys>::new(*self as _));
                    ((bits << (<$tys>::new(*self as _)))&mask )| (val & !mask)
                }
            }
            impl BitfieldPosition<$tys> for Range<u32>{
                fn extract(&self, bits: $tys) -> $tys{
                    let length = self.end-self.start;
                    let mask = (<$tys>::new(1) << (<$tys>::new(length as _) + 1)) - 1;

                    (bits & (mask << (<$tys>::new(self.start as _)))) >> (<$tys>::new(self.start as _))
                }

                fn insert(&self,val: $tys, bits: $tys) -> $tys{
                    let length = self.end-self.start;
                    let mask = (<$tys>::new(1) << (<$tys>::new(length as _) + 1)) - 1;
                    ((bits << (<$tys>::new(self.start as _)))&mask )| (val & !mask)
                }
            }
        )*
    }
}

impl_bitfield_pos! {
    LeU8, LeU16, LeU32, LeU64, LeU128, BeU8, BeU16, BeU32, BeU64, BeU128
}

pub trait FromBitfield<T: BitfieldTy>: Sized {
    fn from_bits(bits: T) -> Self;
    fn to_bits(self) -> T;

    fn validate(self) -> bool {
        true
    }
}

macro_rules! impl_from_bitfield_truncate{
    {
        $($as_ty:ident: $($bitfield_tys:ident),*;)*
    } => {
        $(
            $(
                impl FromBitfield<$bitfield_tys> for $as_ty{
                    fn from_bits(bits: $bitfield_tys) -> Self{
                        bits.unsigned_as()
                    }
                    fn to_bits(self) -> $bitfield_tys{
                        self.unsigned_as()
                    }
                }

            )*
        )*
    }
}

impl_from_bitfield_truncate! {
    LeU8: LeU16, LeU32, LeU64, LeU128;
    LeU16: LeU8, LeU32, LeU64, LeU128;
    LeU32: LeU8, LeU16, LeU64, LeU128;
    LeU64: LeU8, LeU16, LeU32, LeU128;
    LeU128: LeU8, LeU16, LeU32, LeU64;
}

macro_rules! impl_from_bitfield_identity_and_bool{
    {
        $($bitfield_tys:ident),*
    } => {
        $(
            impl FromBitfield<$bitfield_tys> for $bitfield_tys{
                fn from_bits(bits: $bitfield_tys) -> Self{
                    bits
                }
                fn to_bits(self) -> Self{
                    self
                }
            }

            impl FromBitfield<$bitfield_tys> for bool{
                fn from_bits(bits: $bitfield_tys) -> Self{
                    bits != 0
                }
                fn to_bits(self) -> $bitfield_tys{
                    $bitfield_tys::new(self as _)
                }
            }
        )*
    }
}

impl_from_bitfield_identity_and_bool!(
    LeU8, LeU16, LeU32, LeU64, LeU128, BeU8, BeU16, BeU32, BeU64, BeU128
);

macro_rules! impl_bitfield_trunc_to_le{
    {
        $($be_ty:ident: $($le_ty:ident),*;)*
    } => {
        $(
            $(
                impl FromBitfield<$be_ty> for $le_ty{
                    fn from_bits(bits: $be_ty) -> Self{
                        bits.to_le().unsigned_as()
                    }

                    fn to_bits(self) -> $be_ty{
                        <$be_ty>::from_le(self.unsigned_as())
                    }
                }

                impl FromBitfield<$le_ty> for $be_ty{
                    fn from_bits(bits: $le_ty) -> Self{
                        <$be_ty>::from_le(bits.unsigned_as())
                    }
                    fn to_bits(self) -> $le_ty{
                        self.to_le().unsigned_as()
                    }
                }
            )*
        )*
    }
}

impl_bitfield_trunc_to_le! {
    BeU8  : LeU128, LeU64, LeU32, LeU16, LeU8;
    BeU16 : LeU128, LeU64, LeU32, LeU16, LeU8;
    BeU32 : LeU128, LeU64, LeU32, LeU16, LeU8;
    BeU64 : LeU128, LeU64, LeU32, LeU16, LeU8;
    BeU128: LeU128, LeU64, LeU32, LeU16, LeU8;
}

macro_rules! impl_bitfield_trunc_to_be{
    {
        $($be_ty:ident: $($be_ty2:ident),*;)*
    } => {
        $(
            $(
                impl FromBitfield<$be_ty> for $be_ty2{
                    fn from_bits(bits: $be_ty) -> Self{
                        Self::from_le(bits.to_le().unsigned_as())
                    }

                    fn to_bits(self) -> $be_ty{
                        <$be_ty>::from_le(self.to_le().unsigned_as())
                    }
                }

            )*
        )*
    }
}

impl_bitfield_trunc_to_be! {
    BeU8  : BeU128, BeU64, BeU32, BeU16;
    BeU16 : BeU128, BeU64, BeU32, BeU8 ;
    BeU32 : BeU128, BeU64, BeU16, BeU8 ;
    BeU64 : BeU128, BeU32, BeU16, BeU8 ;
    BeU128: BeU64 , BeU32, BeU16, BeU8 ;
}

/// A bitfield element that is a "Sentinel"
///
/// It does not appear in
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Sentinel<T>(pub T);

unsafe impl<T: bytemuck::Pod> bytemuck::Pod for Sentinel<T> {}
unsafe impl<T: bytemuck::Zeroable> bytemuck::Zeroable for Sentinel<T> {}

impl<R: BitfieldTy, T: FromBitfield<R>> FromBitfield<R> for Sentinel<T> {
    fn from_bits(bits: R) -> Self {
        Self(T::from_bits(bits))
    }

    fn to_bits(self) -> R {
        self.0.to_bits()
    }

    fn validate(self) -> bool {
        self.0.validate()
    }
}

impl<T> DisplayBitfield for Sentinel<T> {
    fn present(&self) -> bool {
        false
    }
    fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        Ok(())
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct FixedField<T, const N: u64>(pub T);

unsafe impl<T: bytemuck::Pod, const N: u64> bytemuck::Pod for FixedField<T, N> {}
unsafe impl<T: bytemuck::Zeroable, const N: u64> bytemuck::Zeroable for FixedField<T, N> {}

impl<R: BitfieldTy + Pod, T: FromBitfield<R>, const N: u64> FromBitfield<R> for FixedField<T, N>
where
    LeU64: FromBitfield<R>,
    R: PartialEq,
    T: Copy,
{
    fn from_bits(bits: R) -> Self {
        Self(T::from_bits(bits))
    }

    fn to_bits(self) -> R {
        self.0.to_bits()
    }

    fn validate(self) -> bool {
        self.0.validate() && (LeU64::from_bits(self.to_bits()) == LeU64::new(N))
    }
}

impl<T, const N: u64> DisplayBitfield for FixedField<T, N> {
    fn present(&self) -> bool {
        false
    }
    fn display(&self, _: &str, _: &mut core::fmt::Formatter) -> core::fmt::Result {
        Ok(())
    }
}

pub trait DisplayBitfield {
    fn present(&self) -> bool;
    fn display(&self, name: &str, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result;
}

impl<T: DisplayBitfield> DisplayBitfield for Option<T> {
    fn present(&self) -> bool {
        self.as_ref().map(T::present).unwrap_or(false)
    }

    fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        self.as_ref().unwrap().display(name, f)
    }
}

impl DisplayBitfield for bool {
    fn present(&self) -> bool {
        *self
    }

    fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_str(name)
    }
}

macro_rules! impl_display_bitfield_integer {
    ($($ty:ty),*) => {
        $(
            impl DisplayBitfield for $ty {
                fn present(&self) -> bool {
                    true
                }
                fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    f.write_str(name)?;
                    f.write_str("(")?;
                    f.write_fmt(format_args!("{:#X}", self))?;
                    f.write_str(")")
                }
            }
        )*
    };
}

impl_display_bitfield_integer!(
    LeU8, LeU16, LeU32, LeU64, LeU128, BeU8, BeU16, BeU32, BeU64, BeU128
);

#[repr(transparent)]
pub struct BitfieldArray<R, T, const N: usize, const W: u32>(R, PhantomData<[T; N]>);

unsafe impl<R: Zeroable, T: Zeroable, const N: usize, const W: u32> Zeroable
    for BitfieldArray<R, T, N, W>
{
}
unsafe impl<R: Pod, T: Zeroable + Copy + 'static, const N: usize, const W: u32> Pod
    for BitfieldArray<R, T, N, W>
{
}

impl<R: Copy, T: Copy, const N: usize, const W: u32> Copy for BitfieldArray<R, T, N, W> {}
impl<R: Copy, T: Copy, const N: usize, const W: u32> Clone for BitfieldArray<R, T, N, W> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<R, T, const N: usize, const W: u32> BitfieldArray<R, T, N, W> {
    pub const fn new(val: R) -> Self {
        assert!(core::mem::size_of::<R>() * 8 <= (N * W as usize));

        Self(val, PhantomData)
    }

    pub const fn zeroed() -> Self
    where
        R: Zeroable,
    {
        Self::new(crate::const_zeroed_safe())
    }
}

impl<R: BitfieldTy, T: FromBitfield<R>, const N: usize, const W: u32> BitfieldArray<R, T, N, W> {
    pub fn get(&self, n: usize) -> T
    where
        Range<u32>: BitfieldPosition<R>,
    {
        if n > N {
            panic!("index {} is out of range of array of length {}", n, N);
        }

        let bit_index = (n as u32) * W;

        let bit_range = bit_index..(bit_index + W);

        let bits = bit_range.extract(self.0);

        T::from_bits(bits)
    }
    pub fn set(&mut self, n: usize, val: T)
    where
        Range<u32>: BitfieldPosition<R>,
    {
        if n > N {
            panic!("index {} is out of range of array of length {}", n, N);
        }

        let bit_index = (n as u32) * W;

        let bit_range = bit_index..(bit_index + W);

        self.0 = bit_range.insert(self.0, T::to_bits(val));
    }
}

impl<
        B: BitfieldTy,
        R: BitfieldTy + FromBitfield<B>,
        T: FromBitfield<R>,
        const N: usize,
        const W: u32,
    > FromBitfield<B> for BitfieldArray<R, T, N, W>
where
    Range<u32>: BitfieldPosition<R>,
{
    fn from_bits(bits: B) -> Self {
        Self::new(R::from_bits(bits))
    }
    fn to_bits(self) -> B {
        self.0.to_bits()
    }

    fn validate(self) -> bool {
        let mut b = true;
        for i in 0..N {
            b &= self.get(i).validate();
        }
        b
    }
}

impl<R: BitfieldTy, T: FromBitfield<R> + DisplayBitfield, const N: usize, const W: u32>
    DisplayBitfield for BitfieldArray<R, T, N, W>
where
    Range<u32>: BitfieldPosition<R>,
{
    fn present(&self) -> bool {
        let mut present = false;
        for i in 0..N {
            present |= self.get(i).present();
        }
        present
    }

    fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_str(name)?;
        f.write_str("[")?;
        let mut sep = "";
        for i in 0..N {
            f.write_str(sep)?;
            sep = ", ";
            self.get(i).display("", f)?;
        }
        f.write_str("]")
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct SignExt<T, const W: u32>(T);

impl<T, const W: u32> SignExt<T, W> {
    pub const fn new(val: T) -> Self {
        Self(val)
    }

    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T: core::fmt::Display, const W: u32> DisplayBitfield for SignExt<T, W> {
    fn present(&self) -> bool {
        true
    }

    fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_str(name)?;
        f.write_str(": ")?;
        self.0.fmt(f)
    }
}

macro_rules! impl_sign_extend{
    ($($signed_ty:ty : $unsigned_ty:ty),* $(,)?) => {
        $(
            impl<R: $crate::bitfield::BitfieldTy, const W: u32> FromBitfield<R> for SignExt<$signed_ty,W> where $unsigned_ty: FromBitfield<R>{
                fn validate(self) -> bool{
                    (<$signed_ty>::BITS - (self.0.leading_zeros() + self.0.leading_ones())) <= W
                }

                fn from_bits(bits: R) -> Self {
                    const{assert!(W <= <$signed_ty>::BITS);}
                    let unsigned_val = <$unsigned_ty>::from_bits(bits).cast_sign();

                    let empty_bits = <$signed_ty>::BITS - W;

                    Self::new((unsigned_val << empty_bits) >> empty_bits)
                }

                fn to_bits(self) -> R{
                    let mask = <$unsigned_ty>::new(!0 >> (<$signed_ty>::BITS - W));
                    let unsigned_val = self.0.cast_sign() & mask;

                    unsigned_val.to_bits()
                }
            }
        )*
    };
}

impl_sign_extend! {
    LeI8: LeU8,
    LeI16: LeU16,
    LeI32: LeU32,
    LeI64: LeU64,
    LeI128: LeU128,
    BeI8: BeU8,
    BeI16: BeU16,
    BeI32: BeU32,
    BeI64: BeU64,
    BeI128: BeU128,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Invert<T, const W: u32>(T);

impl<T, const W: u32> Invert<T, W> {
    pub const fn new(val: T) -> Self {
        Self(val)
    }

    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T: DisplayBitfield, const W: u32> DisplayBitfield for Invert<T, W> {
    fn present(&self) -> bool {
        self.0.present()
    }

    fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        self.0.display(name, f)
    }
}

impl<R: BitfieldTy, T: FromBitfield<R>, const W: u32> FromBitfield<R> for Invert<T, W> {
    fn validate(self) -> bool {
        self.0.validate()
    }

    fn from_bits(bits: R) -> Self {
        let mask = (!R::ZERO) << W;

        let real_val = !(bits | mask);

        Self::new(T::from_bits(real_val))
    }

    fn to_bits(self) -> R {
        let mask = (!R::ZERO) << W;

        let bits = self.0.to_bits();

        let real_val = !(bits | mask);

        real_val
    }
}
