
#[repr(C)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct AciDeviceClass{
    pub class: u16,
    pub subclass: u16,
}

pub const BRIDGE_DEVICE: AciDeviceClass = AciDeviceClass{class:0x0004, subclass: 0x0000};

#[repr(C)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct AciDeviceProduct{
    pub vendor: u16,
    pub product: u16,
}

pub type DeviceDmaRegion = [u32;4096];

#[repr(C)]
pub struct AciDevice{
    devid: u16,
    base_addr: *mut [u32;4096],
    class: AciDeviceClass,
    product: AciDeviceProduct
}

pub fn enumerate_devices(&self, space: &mut [AciDevice]) -> &[AciDevice]{
    let base_addr = crate::io::io_read(IoAddr::from_addr())
}