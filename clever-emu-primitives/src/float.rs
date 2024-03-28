use bytemuck::{Pod, Zeroable};

use core::cmp::{Eq, Ord, PartialEq, PartialOrd};
use core::ops::{Add, BitAnd, BitOr, BitXor, Neg, Not, Shl, Shr, Sub};
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
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct CleverFloat<T>(T);

pub unsafe trait FloatRepr:
    Pod
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitXor<Output = Self>
    + Not<Output = Self>
    + Add<Output = Self>
    + Sub<Output = Self>
    + Shr<u32, Output = Self>
    + Shl<u32, Output = Self>
    + Eq
    + Ord
{
    const MANT_BITS: u32;
    const EXP_BITS: u32;
    const EXP_BIAS: Self;

    const ZERO: Self;
    const ONE: Self;
}

unsafe impl<T: Zeroable> Zeroable for CleverFloat<T> {}
unsafe impl<T: Pod> Pod for CleverFloat<T> {}

unsafe impl FloatRepr for LeU16 {
    const MANT_BITS: u32 = 10;
    const EXP_BITS: u32 = 5;
    const EXP_BIAS: Self = Self::new(15);
    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);
}

unsafe impl FloatRepr for LeU32 {
    const MANT_BITS: u32 = 23;
    const EXP_BITS: u32 = 8;
    const EXP_BIAS: Self = Self::new(127);
    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);
}

unsafe impl FloatRepr for LeU64 {
    const MANT_BITS: u32 = 52;
    const EXP_BITS: u32 = 11;
    const EXP_BIAS: Self = Self::new(1023);
    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);
}

unsafe impl FloatRepr for LeU128 {
    const MANT_BITS: u32 = 113;
    const EXP_BITS: u32 = 15;
    const EXP_BIAS: Self = Self::new(16383);
    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);
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

    pub const RADIX: u32 = 0;
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

    pub fn add_round(self, other: Self, rnd: RoundingMode) -> FloatResult<Self> {
        let (this_sign, mut this_exp, this_mant) = self.extract_fields();
        let (other_sign, other_exp, other_mant) = other.extract_fields();

        match (self.classify(), other.classify()) {
            (FpCategory::Nan, _) => Ok(self),
            (_, FpCategory::Nan) => Ok(other),
            (FpCategory::Infinite, FpCategory::Infinite) | (FpCategory::Zero, FpCategory::Zero)
                if this_sign == other_sign =>
            {
                Ok(self)
            }
            (FpCategory::Infinite, FpCategory::Infinite) => {
                let nan = Self::non_const_nan();

                Err((FpException::with_invalid(true), nan))
            }
            (FpCategory::Infinite, _) => Ok(self),
            (_, FpCategory::Infinite) => Ok(other),
            (FpCategory::Zero, FpCategory::Zero) => Ok(Self::ZERO),
            (FpCategory::Zero, _) => Ok(other),
            (_, FpCategory::Zero) => Ok(self),
            (FpCategory::Subnormal, _) | (_, FpCategory::Subnormal) => {
                todo!("Figure out subnormals")
            }
            (_, _) => {
                let real_mant_mask = !T::ZERO >> (T::EXP_BITS - 1);
                let mant_mask = real_mant_mask >> 2;
                let this_real_mant = (this_mant | (T::ONE << T::MANT_BITS)) << 1;
                let other_real_mant = (this_mant | (T::ONE << T::MANT_BITS)) << 1;
                let (sign, mut exp, mut sum_mant, mut inexact) = match (
                    this_exp == other_exp,
                    this_sign == other_sign,
                ) {
                    (true, true) => (this_sign, this_exp, this_real_mant + other_real_mant, false),
                    (false, true) => {
                        let mut fields = [(this_exp, this_real_mant), (other_exp, other_real_mant)];
                        fields.sort_unstable_by_key(|(exp, _)| *exp); // we know they aren't the same value so unstable sorting is fine
                        let [(mut small_exp, mut small_mant), (large_exp, large_mant)] = fields;

                        let mut inexact = false;

                        while small_exp != large_exp {
                            small_exp = small_exp + T::ONE;
                            inexact |= (small_mant & T::ONE) == T::ONE;
                            small_mant = small_mant >> 1;
                        }

                        (this_sign, large_exp, large_mant + small_mant, inexact)
                    }
                    (true, false) => {
                        if this_real_mant == other_real_mant {
                            return Ok(Self::ZERO);
                        }

                        let mut fields: [(bool, T); 2] =
                            [(this_sign, this_real_mant), (other_sign, other_real_mant)];
                        fields.sort_unstable_by_key(|(_, mant)| *mant);
                        let [(_, small_mant), (large_sign, large_mant)] = fields;

                        (large_sign, this_exp, large_mant - small_mant, false)
                    }
                    (false, false) => {
                        let mut fields = [
                            (this_sign, this_exp, this_real_mant),
                            (other_sign, other_exp, other_real_mant),
                        ];
                        fields.sort_unstable_by_key(|(_, exp, _)| *exp); // we know they aren't the same value so unstable sorting is fine
                        let [(_, mut small_exp, mut small_mant), (large_sign, large_exp, large_mant)] =
                            fields;

                        let mut inexact = false;

                        while small_exp != large_exp {
                            small_exp = small_exp + T::ONE;
                            inexact |= (small_mant & T::ONE) == T::ONE;
                            small_mant = small_mant >> 1;
                        }

                        (large_sign, large_exp, large_mant - small_mant, inexact)
                    }
                };

                let unrounded = Self::from_fields(sign, exp, (sum_mant >> 1) & mant_mask);

                if sum_mant == T::ZERO {
                    if inexact {
                        let val = match rnd {
                            RoundingMode::ToNInf => Self(T::ONE).negate(),
                            RoundingMode::ToInf => Self(T::ONE),
                            RoundingMode::HalfToEven | RoundingMode::ToZero => Self::ZERO,
                            x => panic!("Invalid rounding mode {:?}", x),
                        };

                        return Err((FpException::with_underflow(true), val));
                    } else {
                        return Ok(Self::ZERO.copysign(unrounded));
                    }
                }

                if (sum_mant & !real_mant_mask) != T::ZERO {
                    inexact |= (sum_mant & T::ONE) == T::ONE;
                    sum_mant = sum_mant >> 1;
                    exp = exp + T::ONE;
                }

                if exp >= Self::exp_exponent() {
                    return Err((
                        FpException::with_overflow(true),
                        Self::non_const_plus_infinity().copysign(unrounded),
                    ));
                }

                let low_bit = sum_mant & T::ONE;
                inexact |= low_bit == T::ONE;
                sum_mant = sum_mant >> 1;

                if inexact {
                    let inc = match rnd {
                        RoundingMode::HalfToEven => sum_mant & low_bit & T::ONE,
                        RoundingMode::ToInf if !this_sign => T::ZERO,
                        RoundingMode::ToNInf if this_sign => T::ONE,
                        RoundingMode::ToInf | RoundingMode::ToNInf | RoundingMode::ToZero => {
                            T::ZERO
                        }

                        x => panic!("Invalid rounding mode {:?}", x),
                    };

                    sum_mant = sum_mant + inc;
                    if (sum_mant & !(real_mant_mask >> 1)) != T::ZERO {
                        sum_mant = sum_mant >> 1;
                        exp = exp + T::ONE;
                    }

                    if this_exp >= Self::exp_exponent() {
                        Err((
                            FpException::with_overflow(true) | FpException::with_inexact(true),
                            Self::non_const_plus_infinity().copysign(unrounded),
                        ))
                    } else {
                        Err((
                            FpException::with_inexact(true),
                            Self::from_fields(sign, exp, sum_mant),
                        ))
                    }
                } else {
                    Ok(Self::from_fields(sign, exp, sum_mant))
                }
            }
        }
    }

    pub fn sub_round(self, other: Self, rnd: RoundingMode) -> FloatResult<Self> {
        if other.is_nan() {
            return Ok(other);
        }

        self.add_round(-other, rnd)
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
            pub fn $from_float_name(val: $float_ty) -> Self{
                Self(<$base_ty>::new(val.to_bits()))
            }

            pub fn $to_float_name(self) -> $float_ty{
                <$float_ty>::from_bits(self.0.get())
            }
        })*
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
        assert_eq!(
            CleverF32::from_f32(1.0) + CleverF32::from_f32(1.0),
            CleverF32::from_f32(2.0)
        )
    }
}
