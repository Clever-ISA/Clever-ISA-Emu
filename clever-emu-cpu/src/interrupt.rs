use bytemuck::Pod;
use bytemuck::Zeroable;
use clever_emu_primitives::bitfield;

use clever_emu_primitives::primitive::*;
use clever_emu_types::ExecutionMode;

bitfield!{
    pub struct ItabEntryFlags : LeU64{
        pub present @ 0: bool,
        pub px @ 1..2: ExecutionMode
    }
}

#[repr(C,align(32))]
#[derive(Pod, Zeroable, Copy, Clone)]
pub struct ItabEntry{
    pub ip: LeI64,
    pub sp: LeI64,
    pub flags: ItabEntryFlags,
    pub mode: LeU64,
}

impl ItabEntry{
    pub const SIZE: LeU64 = LeU64::new(core::mem::size_of::<Self>() as u64);
}

#[repr(C,align(32))]
#[derive(Pod, Zeroable, Copy, Clone)]
pub struct ItabHeader{
    pub size: LeU64,
    #[doc(hidden)]
    pub __reserved: [LeU64;3]
}