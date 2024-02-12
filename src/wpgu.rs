use clever_isa_emu::{bitfield::bitfield, primitive::*};
use wgpu::Texture;

const CLASS: u32 = 0x0006;
const SUBCLASS: u32 = 0x0001;
const VENDOR: u32 = 0x8001;
const PRODUCT: u32 = 0x0001;

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Color(LeU32);

bitfield! {
    pub struct FramebufferSize: LeU32{
        pub width @ 0..16 : LeU16,
        pub height @ 16..32: LeU16,
    }
}

bitfield! {
    pub struct FramebufferOptions : LeU32{
        pub color_bpp @ 0..2: LeU8,
    }
}

pub struct WpguDevice {
    framebuffer_devid: LeU16,
    shader_target_devid: LeU16,
    hid_devid: LeU16,
    screen_size: FramebufferSize,
    frame_buffer: Texture,
    fb_operation: FramebufferOptions,
    shader_buf: Vec<u32>,
}
