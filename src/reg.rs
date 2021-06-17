use std::{
    ops::{Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
};

use bytemuck::{Pod, Zeroable};

use crate::error::{CPUException, CPUResult};

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
}

#[derive(Copy, Clone)]
#[repr(C)]
pub union RegsRaw {
    pub named: RegsNamed,
    pub array: [u64; 64],
}

unsafe impl Zeroable for RegsRaw {}
unsafe impl Pod for RegsRaw {}

impl<I: SliceIndex<[u64]>> Index<I> for RegsRaw {
    type Output = <I as SliceIndex<[u64]>>::Output;

    #[inline]
    fn index(&self, idx: I) -> &Self::Output {
        unsafe { &self.array[idx] }
    }
}

impl<I: SliceIndex<[u64]>> IndexMut<I> for RegsRaw {
    #[inline]
    fn index_mut(&mut self, idx: I) -> &mut Self::Output {
        unsafe { &mut self.array[idx] }
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
    pub fn from_array(array: [u64; 64]) -> RegsRaw {
        RegsRaw { array }
    }

    pub fn get_if_valid(&self, idx: usize) -> CPUResult<&u64> {
        match idx {
            18..=23 | 52..=55 => Err(CPUException::Undefined),
            #[cfg(not(feature = "fp"))]
            24..=31 => Err(CPUException::Undefined),
            idx @ 0..=62 => Ok(&self[idx]),
            _ => Err(CPUException::Undefined),
        }
    }

    pub fn get_mut_if_valid(&mut self, idx: usize) -> CPUResult<&mut u64> {
        match idx {
            18..=23 | 52..=55 => Err(CPUException::Undefined),
            #[cfg(not(feature = "fp"))]
            24..=31 => Err(CPUException::Undefined),
            idx @ 0..=62 => Ok(&mut self[idx]),
            _ => Err(CPUException::Undefined),
        }
    }
}
