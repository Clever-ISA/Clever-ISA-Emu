use aci_registry::{non_authorative::CleverIsaProduct, DeviceClass, DeviceVendor, SubclassId};
use wgpu::Device;
use winit::window::Window;

use aci_firmware_hal::device;

pub struct WgpuDevice {
    window: Window,
    backing: Device,
}

impl WgpuDevice {
    pub fn new() -> Self {
        todo!()
    }
}

impl device::Device for WgpuDevice {
    fn device_class(&self) -> (aci_registry::DeviceClass, aci_registry::SubclassId) {
        (DeviceClass::Graphics, SubclassId::from_id(0)) // TODO: Actually fill this in
    }

    fn device_product(&self) -> (aci_registry::DeviceVendor, aci_registry::ProductId) {
        (
            DeviceVendor::CleverIsa,
            CleverIsaProduct::CleverEmuFramebuffer.into_generic(),
        )
    }

    fn read(
        &self,
        addr: u16, /* actually a u12 */
        port: &dyn aci_firmware_hal::connection::DevicePort,
    ) -> u32 {
        todo!()
    }
    fn write(
        &self,
        addr: u16, /* actually a u12 */
        val: u32,
        port: &dyn aci_firmware_hal::connection::DevicePort,
    ) {
        todo!()
    }
}
