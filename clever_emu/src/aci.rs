use std::rc::Rc;

use crate::primitive::*;

use aci_firmware_hal::device::Device;

pub struct AciPort {
    attached: Box<dyn Device + Sync>,
    devid: u16,
}

pub struct AciBridge {
    bridged: Vec<AciPort>,
}
