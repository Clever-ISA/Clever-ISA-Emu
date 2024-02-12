use bytemuck::{Pod, Zeroable};

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

pub unsafe trait FloatRepr: Pod {
    const MANT_BITS: u32;
    const EXP_BITS: u32;
    const EXP_BIAS: Self;
}

unsafe impl<T: Zeroable> Zeroable for CleverFloat<T> {}
unsafe impl<T: Pod> Pod for CleverFloat<T> {}

unsafe impl FloatRepr for LeI16 {
    const MANT_BITS: u32 = 10;
    const EXP_BITS: u32 = 5;
    const EXP_BIAS: Self = Self::new(15);
}

unsafe impl FloatRepr for LeI32 {
    const MANT_BITS: u32 = 23;
    const EXP_BITS: u32 = 8;
    const EXP_BIAS: Self = Self::new(127);
}

unsafe impl FloatRepr for LeI64 {
    const MANT_BITS: u32 = 52;
    const EXP_BITS: u32 = 11;
    const EXP_BIAS: Self = Self::new(1023);
}

unsafe impl FloatRepr for LeI128 {
    const MANT_BITS: u32 = 113;
    const EXP_BITS: u32 = 15;
    const EXP_BIAS: Self = Self::new(16383);
}

impl<T> CleverFloat<T> {
    pub const fn from_bits(x: T) -> Self {
        Self(x)
    }

    pub fn into_bits(self) -> T {
        self.0
    }
}

impl<T: FloatRepr> CleverFloat<T> {}

pub type CleverF16 = CleverFloat<LeI16>;
pub type CleverF32 = CleverFloat<LeI32>;
pub type CleverF64 = CleverFloat<LeI64>;
pub type CleverF128 = CleverFloat<LeI128>;

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
        CleverF64::from_bits(self.0)
    }

    pub const fn into_f32(self) -> CleverF32 {
        CleverF32::from_bits(self.0.truncate_to())
    }

    pub const fn into_f16(self) -> CleverF16 {
        CleverF16::from_bits(self.0.truncate_to())
    }
}
