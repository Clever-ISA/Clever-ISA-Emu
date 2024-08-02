use wgpu::Device;
use winit::window::Window;

pub struct WgpuDevice {
    window: Window,
    backing: Device,
}
