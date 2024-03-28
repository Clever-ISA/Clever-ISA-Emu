#![allow(unstable_name_collisions)]
use bytemuck::{AnyBitPattern, NoUninit};
use sptr::Strict;

#[repr(transparent)]
pub struct Racy<T>(T);

impl<T> Racy<T> {
    pub const fn new(x: T) -> Self {
        Self(x)
    }

    pub fn into_inner(self) -> T {
        self.0
    }

    pub fn get_mut(&mut self) -> &mut T {
        &mut self.0
    }

    pub const unsafe fn get(&self) -> &T {
        &self.0
    }
}

unsafe impl<T> Sync for Racy<T> {}

#[cold]
fn align_byte_offset_slow(x: *const u8, align: usize) -> usize {
    let base = x.addr();

    (base + (align - 1)) & !align
}

fn align_byte_offset(x: *const u8, align: usize) -> usize {
    let off = x.align_offset(align);

    if off == !0 {
        align_byte_offset_slow(x, align)
    } else {
        off
    }
}

pub fn align_to_split<T: AnyBitPattern>(x: &[u8]) -> (&[u8], &[T], &[u8]) {
    let base: *const u8 = x.as_ptr();
    let off = align_byte_offset(base, core::mem::align_of::<T>());
    if off == !0 {}

    if off < x.len() {
        let (begin, rest) = x.split_at(off);
        let size = core::mem::size_of::<T>();
        let len = rest.len();

        let tail_len = len % size;
        let middle_len = len - tail_len;

        let (middle, tail) = rest.split_at(middle_len);
        (begin, bytemuck::cast_slice(middle), tail)
    } else {
        (x, &[], &[])
    }
}

pub fn align_to_split_mut<T: AnyBitPattern + NoUninit>(
    x: &mut [u8],
) -> (&mut [u8], &mut [T], &mut [u8]) {
    let base = x.as_ptr();
    let off = base.align_offset(core::mem::align_of::<T>());

    if off < x.len() {
        let (begin, rest) = x.split_at_mut(off);
        let size = core::mem::size_of::<T>();
        let len = rest.len();

        let tail_len = len % size;
        let middle_len = len - tail_len;

        let (middle, tail) = rest.split_at_mut(middle_len);
        (begin, bytemuck::cast_slice_mut(middle), tail)
    } else {
        (x, &mut [], &mut [])
    }
}
