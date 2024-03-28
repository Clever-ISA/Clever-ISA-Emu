use aci_firmware_hal::{connection::DevicePort, device::Device};

use aci_registry::{
    non_authorative::CleverIsaProduct, BridgeSubclass, DeviceClass, DeviceVendor, ProductId,
    SubclassId,
};
use clever_emu_primitives::sync::atomic::AtomicLeU64;

use core::sync::atomic::{AtomicU16, AtomicU32, Ordering};

pub struct Port {
    device: Box<dyn Device + Send>,
    status: AtomicU32,
}

impl DevicePort for Port {
    fn interrupt_host(&self) {
        self.status.fetch_or(1 << 17, Ordering::Relaxed);
    }
}

pub struct RootBridge {
    attached: Vec<Port>,
    root_devid: AtomicU16,
    last_signaled_interrupt: AtomicU16,
    base_addr: AtomicLeU64,
}

impl Device for RootBridge {
    fn device_class(&self) -> (DeviceClass, SubclassId) {
        (
            DeviceClass::Bridge,
            BridgeSubclass::AciBridge1xN.into_generic(),
        )
    }

    fn device_product(&self) -> (DeviceVendor, ProductId) {
        (
            DeviceVendor::CleverIsa,
            CleverIsaProduct::CleverEmuRoot.into_generic(),
        )
    }

    fn read(
        &self,
        addr: u16, /* actually a u12 */
        _: &dyn aci_firmware_hal::connection::DevicePort,
    ) -> u32 {
        match addr {
            0x10 => self.attached.len() as u32,
            0x11 => self.last_signaled_interrupt.load(Ordering::Relaxed) as u32,

            n @ 0x20..=0x7FF => {
                let idx = (n - 0x20) as usize;

                if idx < self.attached.len() {
                    self.attached[idx].status.load(Ordering::Relaxed)
                } else {
                    !0
                }
            }
            _ => 0,
        }
    }

    fn write(
        &self,
        addr: u16, /* actually a u12 */
        val: u32,
        _: &dyn aci_firmware_hal::connection::DevicePort,
    ) {
        match addr {
            0x11 => {
                let n = val as usize;

                if n < self.attached.len() {
                    let port = &self.attached[n];
                    port.device.interrupt_device(port);
                }
            }
            n @ 0x200..=0x7FF => {
                let idx = (n - 0x20) as usize;

                if idx < self.attached.len() {
                    let port = &self.attached[idx];

                    if val & (1 << 16) != 0 {
                        port.device.interrupt_device(port);
                    }

                    port.status.store(val & !(1 << 16), Ordering::Relaxed);
                }
            }
            _ => {}
        }
    }
}
