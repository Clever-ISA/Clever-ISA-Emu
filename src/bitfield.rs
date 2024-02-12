#[macro_export]
macro_rules! bitfield{
    {
        $(#[$meta:meta])*
        $vis:vis struct $bitfield_ty:ident : $base_ty:ty{
            $($vis2:vis $field_name:ident @ $placement_start:literal $(.. $placement_end:literal)? : $ty:ty ),*
            $(,)?
        }
    } => {

        $(#[$meta])*
        #[derive(Copy, Clone, PartialEq, Eq, Hash, Default, Debug, bytemuck::Zeroable, bytemuck::Pod)]
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
            $vis fn validate(self) -> bool{
                let mut field = <$base_ty>::new(0);
                let mut fields_valid = true;

                $({
                    let placement = $placement_start $(.. $placement_end)?;
                    field |= $crate::bitfield::BitfieldPosition::insert(&placement, <$base_ty>::new(!0));
                    fields_valid |= $crate::bitfield::FromBitfield::<$base_ty>::validate(self. $field_name ());
                })*

                ((self.bits() & !field) == 0) && fields_valid
            }

            $(
                #[inline]
                $vis2 fn $field_name(&self) -> $ty{
                    let placement = $placement_start $(.. $placement_end)?;
                    let bits = $crate::bitfield::BitfieldPosition::extract(&placement,self.0);

                    $crate::bitfield::FromBitfield::from_bits(bits)
                }

                paste::paste!{
                    #[inline]
                    $vis2 fn [<with_ $field_name>](val: $ty) -> Self{
                        let placement = $placement_start $(.. $placement_end)?;

                        let bits = $crate::bitfield::FromBitfield::to_bits(val);

                        Self($crate::bitfield::BitfieldPosition::insert(&placement, bits))
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

use std::ops::Range;

pub use bitfield;

mod private {
    pub trait Sealed {}
}

use bytemuck::Pod;
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

pub trait BitfieldTy: Sealed {}

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
    fn insert(&self, bits: T) -> T;
}

macro_rules! impl_bitfield_pos{
    ($($tys:ty),*) => {
        $(
            impl BitfieldPosition<$tys> for u32{
                fn extract(&self, bits: $tys)-> $tys{
                    let mask = <$tys>::new(1) << (<$tys>::new(*self as _));

                    (bits & mask) >> (<$tys>::new(*self as _))
                }

                fn insert(&self, bits: $tys) -> $tys{
                    let mask = <$tys>::new(1) << (<$tys>::new(*self as _));
                    (bits << (<$tys>::new(*self as _)))&mask
                }
            }
            impl BitfieldPosition<$tys> for Range<u32>{
                fn extract(&self, bits: $tys) -> $tys{
                    let length = self.end-self.start;
                    let mask = (<$tys>::new(1) << (<$tys>::new(length as _) + 1)) - 1;

                    (bits & (mask << (<$tys>::new(self.start as _)))) >> (<$tys>::new(self.start as _))
                }

                fn insert(&self, bits: $tys) -> $tys{
                    let length = self.end-self.start;
                    let mask = (<$tys>::new(1) << (<$tys>::new(length as _) + 1)) - 1;
                    (bits << (<$tys>::new(self.start as _)))&mask
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

macro_rules! impl_from_bitfield_be_to_le{
    {
        $($be_ty:ident => $le_ty:ident),*
    } => {
        $(
            impl FromBitfield<$le_ty> for $be_ty{
                fn from_bits(bits: $le_ty) -> Self{
                    bits.to_be()
                }
                fn to_bits(self) -> $le_ty{
                    self.to_le()
                }
            }
            impl FromBitfield<$be_ty> for $le_ty{
                fn from_bits(bits: $be_ty) -> Self{
                    bits.to_le()
                }

                fn to_bits(self) -> $be_ty{
                    self.to_be()
                }
            }
        )*
    }
}

impl_from_bitfield_be_to_le! {
    BeU8 => LeU8,
    BeU16 => LeU16,
    BeU32 => LeU32,
    BeU64 => LeU64,
    BeU128 => LeU128
}

macro_rules! impl_bitfield_trunc_to_le{
    {
        $($be_ty:ident: $($le_ty:ident),*;)*
    } => {
        $(
            $(
                impl FromBitfield<$be_ty> for $le_ty{
                    fn from_bits(bits: $be_ty) -> Self{
                        bits.to_le().truncate_to()
                    }

                    fn to_bits(self) -> $be_ty{
                        <$be_ty>::from_le(self.unsigned_as())
                    }
                }
            )*
        )*
    }
}

impl_bitfield_trunc_to_le! {
    BeU16: LeU8;
    BeU32: LeU16, LeU8;
    BeU64: LeU32, LeU16, LeU8;
    BeU128: LeU64, LeU32, LeU16, LeU8;
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
    LeU64: UnsignedAs<R>,
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
        self.0.validate() && (self.to_bits() == LeU64::new(N).unsigned_as::<R>())
    }
}

impl<T, const N: u64> DisplayBitfield for FixedField<T, N> {
    fn present(&self) -> bool {
        false
    }
    fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
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

impl_display_bitfield_integer!(LeU8, LeU16, LeU32, LeU64, LeU128);
