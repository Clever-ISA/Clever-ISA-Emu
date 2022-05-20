use std::{
    fmt::{Debug, Formatter},
    ops::{Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
};

use arch_ops::clever::CleverRegister;
#[cfg(feature = "float")]
use half::f16;

use crate::error::{CPUException, CPUResult};
use bytemuck::{Pod, Zeroable};

#[repr(C, align(16))]
#[derive(Copy, Clone)]
pub union Vector128 {
    pub i64v2: [u64; 2],
    pub i32v4: [u32; 4],
    pub i16v8: [u16; 8],
    pub i8v16: [u8; 16],
    #[cfg(feature = "float")]
    pub f64v2: [f64; 2],
    #[cfg(feature = "float")]
    pub f32v4: [f32; 4],
    #[cfg(feature = "float")]
    pub f16v2: [f16; 8],
}

impl Debug for Vector128 {
    fn fmt(&self, fmt: &mut Formatter) -> core::fmt::Result {
        unsafe { self.i64v2 }.fmt(fmt)
    }
}

unsafe impl Zeroable for Vector128 {}
unsafe impl Pod for Vector128 {}

bitflags::bitflags! {
    #[derive(Zeroable, Pod)]
    #[repr(transparent)]
    pub struct Mode : u64 {
        const XM  = 0x100000000;
        const XMM = 0x200000000;
    }
}

bitflags::bitflags! {
    #[derive(Zeroable, Pod)]
    #[repr(transparent)]
    pub struct Flags: u64 {
        const C = 0x01;
        const Z = 0x02;
        const V = 0x04;
        const N = 0x08;
        const P = 0x10;
    }
}

impl Flags {
    pub const ARITH_FLAGS: Flags = Flags { bits: 0x1F };
    pub const MOV_FLAGS: Flags = Flags { bits: 0x1A };
}

#[derive(Copy, Clone, Zeroable, Pod, Debug)]
#[non_exhaustive]
#[repr(C, align(2048))]
pub struct RegsNamed {
    pub gprs: [u64; 16],
    pub ip: i64,
    pub flags: Flags,
    pub mode: Mode,
    pub fpcw: u64,
    reserved20_23: [u64; 6],
    pub fp: [u64; 8],
    reserved32_62: [u64; 31],
    pub undefined63: u64,
    pub vector: [Vector128; 16],
    reserved96_127: [u64; 32],
    pub cr: [u64; 8],
    pub cpuinfo: [u64; 8],
    pub crx: [u64; 4],
    pub mscr: [u64; 6],
    reserved155: u64,
    pub rdinfo: u64,
    reserved157_254: [u64; 97],
    pub undefined255: u64,
}

const _: () = {
    assert!(core::mem::size_of::<RegsNamed>() == core::mem::size_of::<RegsRaw>());
};

#[derive(Copy, Clone)]
#[repr(C)]
pub union RegsRaw {
    pub named: RegsNamed,
    array: [u64; 256],
}

impl RegsRaw {
    pub const fn new() -> Self {
        Self { array: [0; 256] }
    }

    pub const fn user_registers(&self) -> &[u64; 128] {
        unsafe { &*(self as *const RegsRaw as *const [u64; 128]) }
    }

    pub fn user_registers_mut(&mut self) -> &mut [u64; 128] {
        unsafe { &mut *(self as *mut RegsRaw as *mut [u64; 128]) }
    }
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

impl Index<CleverRegister> for RegsRaw {
    type Output = u64;
    #[inline]
    fn index(&self, idx: CleverRegister) -> &Self::Output {
        unsafe { &self.array[idx.0 as usize] }
    }
}

impl IndexMut<u16> for RegsRaw {
    #[inline]
    fn index_mut(&mut self, idx: u16) -> &mut Self::Output {
        unsafe { &mut self.array[idx as usize] }
    }
}

impl IndexMut<CleverRegister> for RegsRaw {
    #[inline]
    fn index_mut(&mut self, idx: CleverRegister) -> &mut Self::Output {
        unsafe { &mut self.array[idx.0 as usize] }
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
    pub fn from_array(array: [u64; 256]) -> RegsRaw {
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
