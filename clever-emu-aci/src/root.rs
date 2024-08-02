use aci_firmware_hal::{connection::DevicePort, device::Device};

use aci_registry::{
    non_authorative::CleverIsaProduct, BridgeSubclass, DeviceClass, DeviceVendor, ProductId,
    SubclassId,
};
use clever_emu_mem::{
    cache::CacheAccessError,
    io::{IoPort, MmioDevice},
};
use clever_emu_primitives::{
    primitive::{LeU32, LeU64},
    sync::atomic::AtomicLeU64,
};

use clever_emu_types::SizeControl;

use core::sync::atomic::{AtomicU16, AtomicU32, Ordering};

pub struct Port {
    device: Box<dyn Device + Sync>,
    status: AtomicU32,
}

impl Port {
    pub fn try_write_to_device(
        &self,
        devid: u16,
        addr: u16, /* actually a u12 */
        value: u32,
    ) -> bool {
        let status = self.status.load(Ordering::Relaxed);
        if devid == 0xFFFF || (status as u16) == devid {
            if addr >= 16 {
                self.device.write(addr, value, self);
            }

            true
        } else {
            false
        }
    }

    pub fn try_read_from_device(
        &self,
        devid: u16,
        addr: u16, /* actually a u12 */
    ) -> Option<u32> {
        let status = self.status.load(Ordering::Relaxed);
        if devid == 0xFFFF || (status as u16) == devid {
            match addr {
                0 => {
                    let (cl, subcl) = self.device.device_class();
                    Some(((cl.id() as u32) << 16) | (subcl.id() as u32))
                }
                1 => {
                    let (vendor, product) = self.device.device_product();

                    Some(((vendor.id() as u32) << 16) | (product.id() as u32))
                }
                2 => Some(aci_firmware_hal::aci::ACI_VERSION),
                3..=15 => Some(0),
                addr => Some(self.device.read(addr, self)),
            }
        } else {
            None
        }
    }
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
    next_devid: u16,
}

impl RootBridge {
    pub const fn new() -> Self {
        Self {
            attached: Vec::new(),
            root_devid: AtomicU16::new(0),
            last_signaled_interrupt: AtomicU16::new(!0),
            base_addr: AtomicLeU64::new(LeU64::new(0x40000000)),
            next_devid: 1,
        }
    }

    pub fn attach<T: Device + Sync + 'static>(&mut self, dev: T) {
        if self.next_devid > 2016 {
            panic!("We've attached too many devices - maximum supported is 65536 devices")
        }

        let devid = self.next_devid;
        self.next_devid += 1;
        let port = Port {
            status: AtomicU32::new(devid as u32 | 0x10000),
            device: Box::new(dev),
        };

        self.attached.push(port);
    }
}

impl DevicePort for RootBridge {
    fn interrupt_host(&self) {}
}

impl MmioDevice for RootBridge {
    fn responds_to_addr(
        &self,
        addr: clever_emu_primitives::primitive::LeU64,
    ) -> Result<bool, clever_emu_mem::cache::CacheAccessError> {
        let base_addr = self.base_addr.load(Ordering::Relaxed);
        let addr_range = base_addr..(base_addr + LeU64::new(0x10000000));

        if addr_range.contains(&addr) {
            if (addr & LeU64::new(3)) != LeU64::new(0) {
                Err(CacheAccessError::Unavail)
            } else {
                Ok(true)
            }
        } else {
            Ok(false)
        }
    }

    fn read(
        &self,
        addr: clever_emu_primitives::primitive::LeU64,
        data: &mut [u8],
    ) -> Result<(), CacheAccessError> {
        if data.len() != 4 || (addr & LeU64::new(3)) != LeU64::new(0) {
            Err(CacheAccessError::Unavail)
        } else {
            let base_addr = self.base_addr.load(Ordering::Acquire);
            let addr_range = base_addr..(base_addr + LeU64::new(0x10000000));

            if !addr_range.contains(&addr) {
                return Err(CacheAccessError::NotPresent);
            }

            let disposition = ((addr - base_addr) >> 2).get();

            let dma_addr = disposition as u16 & 0xFFF;
            let devid = (disposition >> 12) as u16;

            let val = if devid == self.root_devid.load(Ordering::Relaxed) {
                Device::read(self, dma_addr, self)
            } else {
                self.attached
                    .iter()
                    .filter_map(|f| f.try_read_from_device(devid, dma_addr))
                    .next()
                    .unwrap_or(!0)
            };

            data.copy_from_slice(&val.to_le_bytes());

            Ok(())
        }
    }

    fn write(&self, addr: LeU64, data: &[u8]) -> Result<(), CacheAccessError> {
        if data.len() != 4 || (addr & LeU64::new(3)) != LeU64::new(0) {
            Err(CacheAccessError::Unavail)
        } else {
            let base_addr = self.base_addr.load(Ordering::Acquire);
            let addr_range = base_addr..(base_addr + LeU64::new(0x10000000));

            if !addr_range.contains(&addr) {
                return Err(CacheAccessError::NotPresent);
            }

            let disposition = ((addr - base_addr) >> 2).get();

            let dma_addr = disposition as u16 & 0xFFF;
            let devid = (disposition >> 12) as u16;

            let val: LeU32 = *bytemuck::from_bytes(data);

            if devid == self.root_devid.load(Ordering::Relaxed) {
                Device::write(self, dma_addr, val.get(), self)
            } else if devid == 0xFFFF {
                self.attached.iter().for_each(|f| {
                    f.try_write_to_device(devid, dma_addr, val.get());
                });
            } else {
                self.attached
                    .iter()
                    .find(|f| f.try_write_to_device(devid, dma_addr, val.get()));
            };

            Ok(())
        }
    }
}

impl IoPort for RootBridge {
    fn responds_to_port_addr(&self, addr: LeU64) -> bool {
        matches!(addr.get(), 0x7f000028 | 0x7f000029 | 0x100000027)
    }

    fn port_in(&self, addr: LeU64, size: SizeControl) -> LeU64 {
        match addr.get() {
            0x7f000028 => self.base_addr.load(Ordering::SeqCst) & size.as_regwidth_mask(),
            0x7f000029 => {
                LeU64::new(self.root_devid.load(Ordering::SeqCst) as u64) & size.as_regwidth_mask()
            }
            _ => LeU64::new(0),
        }
    }

    fn port_out(&self, addr: LeU64, data: LeU64, _: SizeControl) {
        match addr.get() {
            0x7f000028 => self.base_addr.store(data, Ordering::SeqCst),
            0x7f000029 => {
                let devid = data.get() as u16;
                self.root_devid.store(devid, Ordering::SeqCst);
            }
            _ => {}
        }
    }
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
            0 => {
                let (cl, subcl) = self.device_class();
                ((cl.id() as u32) << 16) | (subcl.id() as u32)
            }
            1 => {
                let (vendor, product) = self.device_product();

                ((vendor.id() as u32) << 16) | (product.id() as u32)
            }
            2 => aci_firmware_hal::aci::ACI_VERSION,
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

    fn poll_interrupts(&self, port: &dyn DevicePort) {}
}
