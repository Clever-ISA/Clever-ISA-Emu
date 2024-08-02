use bytemuck::{Pod, Zeroable};

use core::cmp::{Eq, Ord, PartialEq, PartialOrd};
use core::ops::{
    Add, AddAssign, BitAnd, BitOr, BitOrAssign, BitXor, Neg, Not, Shl, ShlAssign, Shr, ShrAssign,
    Sub, SubAssign,
};
use std::num::FpCategory;

use crate::bitfield;
use crate::primitive::*;

bitfield! {
    pub struct FpException: LeU8{
        pub invalid @ 0: bool,
        pub div_by_zero @ 1: bool,
        pub overflow @ 2: bool,
        pub underflow @ 3: bool,
        pub inexact @ 4: bool,
        pub signal @ 5: bool,
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    #[derive(Pod, Zeroable)]
    pub enum RoundingMode{
        HalfToEven = 0,
        ToInf = 1,
        ToNInf = 2,
        ToZero = 3,

        Dynamic = 7,
    }
}

mod private {
    use super::{LeU128, LeU16, LeU32, LeU64};

    pub trait Sealed {}

    impl Sealed for LeU16 {}
    impl Sealed for LeU32 {}
    impl Sealed for LeU64 {}
    impl Sealed for LeU128 {}
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct CleverFloat<T>(T);

pub unsafe trait FloatRepr:
    Pod
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + Not<Output = Self>
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Shr<u32, Output = Self>
    + ShrAssign<u32>
    + Shl<u32, Output = Self>
    + ShlAssign<u32>
    + Eq
    + Ord
    + private::Sealed
{
    const BITS: u32;
    const MANT_BITS: u32;
    const EXP_BITS: u32;
    const EXP_BIAS: Self;

    const ZERO: Self;
    const ONE: Self;

    fn from_bits(bits: u32) -> Self;

    fn overflowing_sub(self, other: Self) -> (Self, bool);

    fn overflowing_add(self, other: Self) -> (Self, bool);

    ///
    ///
    /// Returns `(h, l)`, where `h` is the high bits of the result, and `l` is the low bits of the result
    fn widening_mul(self, other: Self) -> (Self, Self);

    fn leading_zeros(self) -> u32;

    fn to_bits(self) -> u32;
}

unsafe impl<T: Zeroable> Zeroable for CleverFloat<T> {}
unsafe impl<T: Pod> Pod for CleverFloat<T> {}

unsafe impl FloatRepr for LeU16 {
    const BITS: u32 = Self::BITS;
    const MANT_BITS: u32 = 10;
    const EXP_BITS: u32 = 5;
    const EXP_BIAS: Self = Self::new(15);
    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);

    fn from_bits(bits: u32) -> Self {
        Self::new(bits.try_into().unwrap())
    }

    fn overflowing_sub(self, other: Self) -> (Self, bool) {
        self.overflowing_sub(other)
    }

    fn overflowing_add(self, other: Self) -> (Self, bool) {
        self.overflowing_add(other)
    }

    fn widening_mul(self, other: Self) -> (Self, Self) {
        let x = self.get() as u32;
        let y = other.get() as u32;

        let mul = x * y;

        (Self::new((mul >> 16) as u16), Self::new(mul as u16))
    }

    fn leading_zeros(self) -> u32 {
        self.leading_zeros()
    }

    fn to_bits(self) -> u32 {
        self.get().into()
    }
}

unsafe impl FloatRepr for LeU32 {
    const BITS: u32 = Self::BITS;
    const MANT_BITS: u32 = 23;
    const EXP_BITS: u32 = 8;
    const EXP_BIAS: Self = Self::new(127);
    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);

    fn from_bits(bits: u32) -> Self {
        Self::new(bits.try_into().unwrap())
    }

    fn overflowing_sub(self, other: Self) -> (Self, bool) {
        self.overflowing_sub(other)
    }

    fn overflowing_add(self, other: Self) -> (Self, bool) {
        self.overflowing_add(other)
    }

    fn widening_mul(self, other: Self) -> (Self, Self) {
        let x = self.get() as u64;
        let y = other.get() as u64;

        let mul = x * y;

        (Self::new((mul >> 32) as u32), Self::new(mul as u32))
    }
    fn leading_zeros(self) -> u32 {
        self.leading_zeros()
    }

    fn to_bits(self) -> u32 {
        self.get()
    }
}

unsafe impl FloatRepr for LeU64 {
    const BITS: u32 = Self::BITS;
    const MANT_BITS: u32 = 52;
    const EXP_BITS: u32 = 11;
    const EXP_BIAS: Self = Self::new(1023);
    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);

    fn from_bits(bits: u32) -> Self {
        Self::new(bits.try_into().unwrap())
    }

    fn widening_mul(self, other: Self) -> (Self, Self) {
        let x = self.get() as u128;
        let y = other.get() as u128;

        let mul = x * y;

        (Self::new((mul >> 64) as u64), Self::new(mul as u64))
    }

    fn overflowing_sub(self, other: Self) -> (Self, bool) {
        self.overflowing_sub(other)
    }

    fn overflowing_add(self, other: Self) -> (Self, bool) {
        self.overflowing_add(other)
    }

    fn leading_zeros(self) -> u32 {
        self.leading_zeros()
    }
    fn to_bits(self) -> u32 {
        self.get().try_into().unwrap()
    }
}

unsafe impl FloatRepr for LeU128 {
    const BITS: u32 = Self::BITS;
    const MANT_BITS: u32 = 113;
    const EXP_BITS: u32 = 15;
    const EXP_BIAS: Self = Self::new(16383);
    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);

    fn from_bits(bits: u32) -> Self {
        use core::convert::TryInto;
        Self::new(bits.try_into().unwrap())
    }

    fn overflowing_sub(self, other: Self) -> (Self, bool) {
        self.overflowing_sub(other)
    }

    fn overflowing_add(self, other: Self) -> (Self, bool) {
        self.overflowing_add(other)
    }

    fn widening_mul(self, other: Self) -> (Self, Self) {
        let this = self.get();
        let other = other.get();

        let this_lo = this & (!0 >> 64);
        let this_hi = this >> 64;
        let other_lo = other & (!0 >> 64);
        let other_hi = other >> 64;

        let res_lo = this_lo * other_lo;

        let res_mid1 = this_lo * other_hi;
        let res_mid2 = this_hi * other_lo;

        let (res_mid, carry) = res_mid1.overflowing_add(res_mid2);

        let res_hi = this_hi * other_hi + (carry as u128);

        let (lo, carry) = res_lo.overflowing_add(res_mid << 64);
        let hi = res_hi + (res_mid >> 64) + (carry as u128);

        (LeU128::new(hi), LeU128::new(lo))
    }
    fn leading_zeros(self) -> u32 {
        self.leading_zeros()
    }

    fn to_bits(self) -> u32 {
        self.get().try_into().unwrap()
    }
}

impl<T: Copy> CleverFloat<T> {
    pub const fn from_bits(x: T) -> Self {
        Self(x)
    }

    pub const fn into_bits(self) -> T {
        self.0
    }
}

impl<T: FloatRepr> CleverFloat<T> {
    pub const ZERO: Self = Self(T::ZERO);

    pub const RADIX: u32 = 2;
    pub const MANTISSA_DIGITS: u32 = T::MANT_BITS + 1;

    fn exp_exponent() -> T {
        let mask = !T::ZERO;

        mask >> (T::MANT_BITS + 1)
    }

    // This is used for generic types that need to produce a NaN constant
    fn non_const_nan() -> Self {
        // 0b1111111111111111
        let mask = !T::ZERO;

        // 0b00000001111111111
        let anti_val = mask >> (T::EXP_BITS + 1);

        // 0b0111111000000000
        let val = (!anti_val) >> 1;

        Self(val)
    }

    fn non_const_plus_infinity() -> Self {
        // 0b1111111111111111
        let mask = !T::ZERO;

        // 0b0000011111111111
        let anti_val = mask >> (T::EXP_BITS);

        // 0b0111110000000000
        let val = (!anti_val) >> 1;

        Self(val)
    }

    fn non_const_neg_infinity() -> Self {
        // 0b1111111111111111
        let mask = !T::ZERO;

        // 0b0000001111111111
        let anti_val = mask >> (T::EXP_BITS + 1);

        // 0b1111110000000000
        let val = !anti_val;

        Self(val)
    }

    fn non_const_one() -> Self {
        let exp = T::EXP_BIAS;

        Self(exp << T::MANT_BITS)
    }

    fn from_fields(sign: bool, exp: T, mant: T) -> Self {
        let sign = if sign { T::ONE } else { T::ZERO };

        let sign_and_exp = (sign << T::EXP_BITS) | exp;

        Self((sign_and_exp << T::MANT_BITS) | mant)
    }

    fn extract_fields(self) -> (bool, T, T) {
        let one = !T::ZERO;
        let mant_mask = one >> (1 + T::EXP_BITS);
        let mant = self.0 & mant_mask;
        let exp_mask = one >> (1 + T::MANT_BITS);
        let exp_and_sign = self.0 >> T::MANT_BITS;
        let exp = exp_and_sign & exp_mask;

        let sign_bit = exp_and_sign >> T::EXP_BITS;

        (sign_bit != T::ZERO, exp, mant)
    }

    pub fn negate(self) -> Self {
        let Self(val) = self;
        let one = T::ONE;

        Self(val ^ (one << (T::EXP_BITS + T::MANT_BITS)))
    }

    pub fn abs(self) -> Self {
        let Self(val) = self;
        let one = !T::ZERO;

        Self(val & (one >> 1))
    }

    pub fn copysign(self, other: Self) -> Self {
        let mask = (!T::ZERO) >> 1;

        let Self(this) = self;
        let Self(other) = other;

        Self((this & mask) | (other & !mask))
    }

    pub fn classify(self) -> FpCategory {
        let (_, exp, mant) = self.extract_fields();

        let one = !T::ZERO;
        let exp_mask = one >> (1 + T::MANT_BITS);

        match (exp == T::ZERO, mant == T::ZERO, exp == exp_mask) {
            (true, true, _) => FpCategory::Zero,
            (true, false, _) => FpCategory::Subnormal,
            (false, true, true) => FpCategory::Infinite,
            (false, false, true) => FpCategory::Nan,
            _ => FpCategory::Normal,
        }
    }

    pub fn is_nan(self) -> bool {
        self.classify() == FpCategory::Nan
    }

    pub fn is_infinite(self) -> bool {
        self.classify() == FpCategory::Infinite
    }

    pub fn is_subnormal(self) -> bool {
        self.classify() == FpCategory::Subnormal
    }

    pub fn is_normal(self) -> bool {
        self.classify() == FpCategory::Normal
    }

    pub fn is_finite(self) -> bool {
        !matches!(self.classify(), FpCategory::Nan | FpCategory::Infinite)
    }

    pub fn total_cmp(&self, other: &Self) -> core::cmp::Ordering {
        let (Self(this), Self(other)) = (*self, *other);

        let sign = T::ONE << (T::MANT_BITS + T::EXP_BITS);

        (this ^ sign).cmp(&(other ^ sign))
    }

    fn mul_add_impl(
        a_mant: T,
        b_mant: T,
        mut c_mant: T,
        mut prod_exp: T,
        c_exp: T,
        prod_sign: bool,
        c_sign: bool,
        rnd: RoundingMode,
    ) -> FloatResult<Self> {
        let (mut prod_hi, mut prod_lo) = T::widening_mul(a_mant, b_mant);

        todo!()
    }

    pub fn mul_add_round(self, b: Self, c: Self, rnd: RoundingMode) -> FloatResult<Self> {
        todo!()
    }

    pub fn add_round(self, b: Self, rnd: RoundingMode) -> FloatResult<Self> {
        self.mul_add_round(Self::non_const_one(), b, rnd)
    }
}

impl<T: FloatRepr> PartialEq for CleverFloat<T> {
    fn eq(&self, other: &Self) -> bool {
        !self.is_nan() && self.0 == other.0
    }
}

impl<T: FloatRepr> PartialOrd for CleverFloat<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self.classify(), other.classify()) {
            (FpCategory::Nan, _) | (_, FpCategory::Nan) => None,
            (FpCategory::Zero, FpCategory::Zero) => Some(std::cmp::Ordering::Equal),
            (_, _) => Some(self.total_cmp(other)),
        }
    }
}

impl<T: FloatRepr> Neg for CleverFloat<T> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.negate()
    }
}

impl<T: FloatRepr> Add for CleverFloat<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match self.add_round(other, RoundingMode::HalfToEven) {
            Ok(val) => val,
            Err((_, val)) => val,
        }
    }
}

pub type CleverF16 = CleverFloat<LeU16>;
pub type CleverF32 = CleverFloat<LeU32>;
pub type CleverF64 = CleverFloat<LeU64>;
pub type CleverF128 = CleverFloat<LeU128>;

macro_rules! impl_concrete_floats {
    ($($base_ty:ty),* $(,)?) => {
        $(impl CleverFloat<$base_ty> {
            pub const INFINITY: Self = Self(<$base_ty>::new(
                !(!0 >> (<$base_ty as FloatRepr>::EXP_BITS)) >> 1,
            ));
            pub const NEG_INFINITY: Self = Self(<$base_ty>::new(
                !(!0 >> (<$base_ty as FloatRepr>::EXP_BITS + 1)),
            ));
            pub const NAN: Self = Self(<$base_ty>::new(
                !(!0 >> (<$base_ty as FloatRepr>::EXP_BITS + 1)) >> 1,
            ));
            pub const MAX: Self = Self(<$base_ty>::new((!0 >> 1) & (1 << (<$base_ty>::MANT_BITS + 1))));
            pub const MIN: Self = Self(<$base_ty>::new((!0) & (1 << (<$base_ty>::MANT_BITS + 1))));
            pub const LEAST: Self = Self(<$base_ty>::new(1));
            pub const EPSILON: Self = Self(<$base_ty>::new(
                ((<$base_ty>::EXP_BIAS.get() - <$base_ty>::new(<$base_ty>::MANT_BITS as _).get()) << <$base_ty>::MANT_BITS)
            ));

            pub const fn to_le_bytes(self) -> [u8; core::mem::size_of::<$base_ty>()] {
                self.into_bits().to_le_bytes()
            }
            pub const fn to_be_bytes(self) -> [u8; core::mem::size_of::<$base_ty>()] {
                self.into_bits().to_be_bytes()
            }
            pub const fn to_ne_bytes(self) -> [u8; core::mem::size_of::<$base_ty>()] {
                self.into_bits().to_ne_bytes()
            }
        })*
    };
}

impl_concrete_floats!(LeU16, LeU32, LeU64, LeU128);

macro_rules! impl_from_lang_floats{
    {$($base_ty:ty => $from_float_name:ident, $to_float_name:ident : $float_ty:ty;)*} => {
        $(impl CleverFloat<$base_ty>{
            pub const fn $from_float_name(val: $float_ty) -> Self{
                Self(<$base_ty>::new($crate::const_transmute_safe(val)))
            }

            pub const fn $to_float_name(self) -> $float_ty{
                $crate::const_transmute_safe(self.0.get())
            }
        }
        impl core::fmt::Debug for CleverFloat<$base_ty>{
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result{
                self.$to_float_name().fmt(f)
            }
        }
        )*
    }
}

impl_from_lang_floats! {
    LeU32 => from_f32, to_f32 : f32;
    LeU64 => from_f64, to_f64 : f64;
}

pub type FloatResult<T> = Result<T, (FpException, T)>;

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Zeroable, Pod)]
pub struct CleverFloatReg(LeI64);

impl CleverFloatReg {
    pub const fn from_bits(x: LeI64) -> Self {
        Self(x)
    }

    pub const fn into_bits(self) -> LeI64 {
        self.0
    }

    pub const fn into_f64(self) -> CleverF64 {
        CleverF64::from_bits(self.0.cast_sign())
    }

    pub const fn into_f32(self) -> CleverF32 {
        CleverF32::from_bits(self.0.truncate_to())
    }

    pub const fn into_f16(self) -> CleverF16 {
        CleverF16::from_bits(self.0.truncate_to())
    }
}

#[cfg(test)]
mod test {
    use super::{CleverF128, CleverF16, CleverF32, CleverF64};
    #[test]
    fn test_add_1_1_f32() {
        let add_1_1 = CleverF32::from_f32(1.0) + CleverF32::from_f32(1.0);
        let const_2 = CleverF32::from_f32(2.0);
        assert_eq!(
            add_1_1,
            const_2,
            "{:?} + {:?} = {:?}",
            CleverF32::from_f32(1.0),
            CleverF32::from_f32(1.0),
            add_1_1
        )
    }

    #[test]
    fn test_add_1_half_f32() {
        let add_1_05 = CleverF32::from_f32(1.0) + CleverF32::from_f32(0.5);
        let const_1_5 = CleverF32::from_f32(1.5);
        assert_eq!(
            add_1_05,
            const_1_5,
            "{:?} + {:?} = {:?}",
            CleverF32::from_f32(1.0),
            CleverF32::from_f32(0.5),
            add_1_05
        )
    }

    #[test]
    fn test_add_1_m1() {
        let add_1_m1 = CleverF32::from_f32(1.0) + CleverF32::from_f32(-1.0);
        let const_0 = CleverF32::from_f32(0.0);
        assert_eq!(
            add_1_m1,
            const_0,
            "{:?} + {:?} = {:?}",
            CleverF32::from_f32(1.0),
            CleverF32::from_f32(-1.0),
            add_1_m1
        )
    }

    #[test]
    fn test_add_inf_ninf() {
        let add_1_m1 = CleverF32::INFINITY + CleverF32::NEG_INFINITY;

        assert!(
            add_1_m1.is_nan(),
            "{:?} + {:?} = {:?}",
            CleverF32::INFINITY,
            CleverF32::NEG_INFINITY,
            add_1_m1
        );
    }
}
