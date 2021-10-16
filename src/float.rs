use std::num::FpCategory;

use rug::{Assign, Float};

use half::f16;

#[derive(Clone, Debug, Copy)]
pub struct CleverFloat(u64, u16);

#[repr(u8)]
pub enum RoundingMode {
    Upwards = 0,
    Downwards = 1,
    Truncate = 2,
    HalfUp = 3,
    HalfToEven = 4,
}

const FORMATS: [(u32, u32, i64, u64); 4] = [
    (0, 0, 0, 0),
    (10, 5, 15, 0x1f),
    (23, 8, 127, 0xff),
    (52, 11, 1023, 0x7ff),
];

bitflags::bitflags! {
    #[repr(transparent)]
    pub struct FpException : u16 {
        const INVALID = 0x01;
        const DIVBYZERO = 0x02;
        const OVERFLOW  = 0x04;
        const UNDERFLOW = 0x08;
        const INEXACT   = 0x10;
        const SIGNAL    = 0x20;
    }
}

pub type FloatResult<T> = Result<T, (FpException, T)>;

impl CleverFloat {
    pub const fn with_size(ss: u16) -> Self {
        Self::from_bits_with_size(0, ss)
    }

    pub const fn from_bits_with_size(bits: u64, ss: u16) -> Self {
        [(); 1][(!(0 < ss && ss < 3)) as usize]; // No I'm not sorry for this const_panic hack

        Self(
            bits & (2u64
                .wrapping_shl(8u32.wrapping_shl(ss as u32) - 1)
                .wrapping_sub(1)),
            ss,
        )
    }

    pub const POSITIVE_INFINITY: Self = positive_infinity(3);
    pub const NEGATIVE_INFINITY: Self = negative_infinity(3);
    pub const NAN: Self = nan(3);

    pub const fn positive_infinity(ss: u16) -> Self {
        [(); 1][(ss == 0) as usize];

        Self(FORMATS[ss].3 << FORMATS[ss].0, ss)
    }

    pub const fn negative_infinity(ss: u16) -> Self {
        [(); 1][(ss == 0) as usize];
        Self(
            (FORMATS[ss].3 << FORMATS[ss].0) | 1u64 << (FORMATS[ss].0 + FORMATS[ss].1),
            ss,
        )
    }

    pub const fn nan(ss: u16) -> Self {
        [(); 1][(ss == 0) as usize];

        Self(
            (1u64 << (FORMATS[self.1].0 - 1)) | (FORMATS[ss].3 << FORMATS[ss].0),
            ss,
        )
    }

    pub const fn negative(self) -> bool {
        self.0 & (1u64.wrapping_shl(8u32.wrapping_shl(ss as u32) - 1)) != 0
    }

    pub const fn exponent(self) -> i64 {
        (self.0 >> (FORMATS[self.1].0))
            & ((1u64 << FORMATS[self.1].1) - 1) as i64 - FORMATS[Self.1].2
    }

    pub const fn classify(self) -> FpCategory {
        let exp = (self.0 >> (FORMATS[self.1].0)) & ((1u64 << FORMATS[self.1].1) - 1);
        let sig = (self.0) & (1u64 << (FORMATS[self.1].0));
        if exp == 0 && sig != 0 {
            return FpCategory::Subnormal;
        } else if exp == 0 {
            return FpCategory::Zero;
        } else if exp == FORMATS[self.1].3 && sig != 0 {
            return FpCategory::Nan;
        } else if exp == FORMATS[self.1].3 {
            return FpCategory::Infinite;
        } else {
            return FpCategory::Normal;
        }
    }

    pub const fn resize(self, ss: u16) -> FloatResult<Self> {
        [(); 1][(ss == 0) as usize]; // more const_panic hacks
                                     // Will t-compiler/const-eval finish bikeshedding soon enough to save panic errors?
                                     // Well...
        let sig = self.0 & (1u64 << FORMATS[self.1].0).wrapping_sub(1);
        Ok(match self.classify() {
            FpCategory::Nan => Self(
                ((self.negative() as u64) << (1u64.wrapping_shl(8u32.wrapping_shl(ss as u32) - 1)))
                    | (1u64 << (FORMATS[self.1].0 - 1))
                    | (FORMATS[ss].3 << FORMATS[ss].0),
                ss,
            ),
            FpCategory::Infinite => Self(
                ((self.negative() as u64) << (1u64.wrapping_shl(8u32.wrapping_shl(ss as u32) - 1)))
                    | (FORMATS[ss].3 << FORMATS[ss].0),
                ss,
            ),
            FpCategory::Zero => Self(
                ((self.negative() as u64) << (1u64.wrapping_shl(8u32.wrapping_shl(ss as u32) - 1))),
                ss,
            ),
            FpCategory::Subnormal => {
                let diffsig = (FORMATS[ss].0 as i32) - (FORMATS[self.1].0 as i32);
                let sig = sig;
                let rsig = if diffsig < 0 {
                    sig >> (-diffsig)
                } else {
                    sig << diffsig
                };

                let val = ((self.negative() as u64)
                    << (1u64.wrapping_shl(8u32.wrapping_shl(ss as u32) - 1)))
                    | rsig; // drop the implicit bit here
                if diffsig < 0 && rsig << (-diffsig) != sig {
                    return Err((FpException::INEXACT, CleverFloat(val, ss)));
                }
                CleverFloat(val, ss)
            }
            FpCategory::Normal => {
                let diffsig = (FORMATS[ss].0 as i32) - (FORMATS[self.1].0 as i32);
                let rsig = if diffsig < 0 {
                    sig >> (-diffsig)
                } else {
                    sig << diffsig
                };
                let exp = self.exponent();
                if exp > FORMATS[ss].2 {
                    return Err((
                        FpException::OVERFLOW,
                        Self(
                            (FORMATS[ss].3 << FORMATS[ss].0)
                                | ((self.negative() as u64)
                                    << (1u64.wrapping_shl(8u32.wrapping_shl(ss as u32) - 1))),
                            ss,
                        ),
                    ));
                } else if exp < -FORMATS[ss].2 {
                    return Err((FpException::UNDERFLOW, Self())); // TODO, we can underflow to DENORMALs as well
                } else {
                    let raw_exp = ((exp + FORMATS[ss].2) as u64) << FORMATS[ss].0;
                    let val = ((self.negative() as u64)
                        << (1u64.wrapping_shl(8u32.wrapping_shl(ss as u32) - 1)))
                        | rsig;

                    if diffsig < 0 && rsig << (-diffsig) != sig {
                        return Err((FpException::INEXACT, CleverFloat(val, ss)));
                    } else {
                        Ok(Self(val, ss))
                    }
                }
            }
        })
    }
}
