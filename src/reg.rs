use std::{
    fmt::{Debug, Formatter},
    ops::{Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
};

use half::f16;

use bytemuck::{Pod, Zeroable};

use crate::error::{CPUException, CPUResult};

#[repr(C, align(128))]
#[derive(Copy, Clone)]
pub union Vector128 {
    pub i64v2: [u64; 2],
    pub i32v4: [u32; 4],
    pub i16v8: [u16; 8],
    pub i8v16: [u8; 16],
    pub f64v2: [f64; 2],
    pub f32v4: [f32; 4],
    pub f16v2: [f16; 8],
}

impl Debug for Vector128 {
    fn fmt(&self, fmt: &mut Formatter) -> core::fmt::Result {
        unsafe { self.i64v2 }.fmt(fmt)
    }
}

unsafe impl Zeroable for Vector128 {}
unsafe impl Pod for Vector128 {}

#[derive(Copy, Clone, Zeroable, Pod, Debug)]
#[repr(C, align(512))]
pub struct RegsNamed {
    pub gprs: [u64; 16],
    pub ip: i64,
    pub flags: u64,
    pub reserved0: [u64; 6],
    pub fp: [u64; 8],
    pub cr: [u64; 8],
    pub cpuinfo: [u64; 8],
    pub crx: [u64; 4],
    pub reserved1: [u64; 5],
    pub mscr: [u64; 6],
    pub undefined: u64,
    pub vector: [Vector128; 32],
}

#[derive(Copy, Clone)]
#[repr(C)]
pub union RegsRaw {
    pub named: RegsNamed,
    pub array: [u64; 128],
}

unsafe impl Zeroable for RegsRaw {}
unsafe impl Pod for RegsRaw {}

impl Index<u16> for RegsRaw {
    type Output = u64;

    #[inline]
    fn index(&self, idx: u16) -> &Self::Output {
        unsafe { &self.array[idx as usize] }
    }
}

impl IndexMut<u16> for RegsRaw {
    #[inline]
    fn index_mut(&mut self, idx: u16) -> &mut Self::Output {
        unsafe { &mut self.array[idx as usize] }
    }
}

impl Deref for RegsRaw {
    type Target = RegsNamed;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &self.named }
    }
}

impl DerefMut for RegsRaw {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut self.named }
    }
}

impl RegsRaw {
    #[inline]
    pub fn from_named(named: RegsNamed) -> RegsRaw {
        RegsRaw { named }
    }

    #[inline]
    pub fn from_array(array: [u64; 128]) -> RegsRaw {
        RegsRaw { array }
    }

    pub fn get_if_valid(&self, idx: u16) -> CPUResult<&u64> {
        match idx {
            18..=23 | 52..=55 => Err(CPUException::Undefined),
            #[cfg(not(feature = "fp"))]
            24..=31 => Err(CPUException::Undefined),
            idx @ 0..=62 => Ok(&self[idx]),
            _ => Err(CPUException::Undefined),
        }
    }

    pub fn get_mut_if_valid(&mut self, idx: u16) -> CPUResult<&mut u64> {
        match idx {
            18..=23 | 52..=55 => Err(CPUException::Undefined),
            #[cfg(not(feature = "fp"))]
            24..=31 => Err(CPUException::Undefined),
            idx @ 0..=62 => Ok(&mut self[idx]),
            _ => Err(CPUException::Undefined),
        }
    }

    pub fn slice<I: SliceIndex<[u64]>>(&self, idx: I) -> &I::Output {
        unsafe { &self.array[idx] }
    }
    pub fn slice_mut<I: SliceIndex<[u64]>>(&mut self, idx: I) -> &mut I::Output {
        unsafe { &mut self.array[idx] }
    }
}
