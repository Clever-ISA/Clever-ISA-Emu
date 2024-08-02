use clever_emu_primitives::primitive::LeU64;

use clever_emu_types::SizeControl;

use crate::cache::{CacheAccessError, CacheAccessResult};

use std::sync::Arc;

pub trait MmioDevice {
    fn responds_to_addr(&self, addr: LeU64) -> Result<bool, CacheAccessError>;
    fn read(&self, addr: LeU64, data: &mut [u8]) -> Result<(), CacheAccessError>;
    fn write(&self, addr: LeU64, data: &[u8]) -> Result<(), CacheAccessError>;

    /// If access to the device returned [`CacheAccessError::Locked`], park the accessing thread in the most efficient way the impl can before the device can be accessed next
    /// Implementing this method is only required if either `read` or `write` can return [`CacheAccessError::Locked`], and only if the thread can do anything more efficient than yield
    fn park_on_unlock(&self) {
        std::thread::yield_now()
    }
}

pub trait IoPort {
    fn responds_to_port_addr(&self, addr: LeU64) -> bool;
    fn port_out(&self, addr: LeU64, data: LeU64, size: SizeControl);
    fn port_in(&self, addr: LeU64, size: SizeControl) -> LeU64;
}

pub struct IoBus {
    ports: Vec<Arc<dyn IoPort + Sync>>,
    mmio: Vec<Arc<dyn MmioDevice + Sync>>,
}

impl IoBus {
    pub const fn new() -> Self {
        Self {
            ports: Vec::new(),
            mmio: Vec::new(),
        }
    }

    pub fn attach_port<T: IoPort + Sync + 'static>(&mut self, port: T) {
        self.attach_shared_port(Arc::new(port))
    }

    pub fn attach_shared_port(&mut self, port: Arc<dyn IoPort + Sync>) {
        self.ports.push(port)
    }

    pub fn attach_mmio<T: MmioDevice + Sync + 'static>(&mut self, mmio: T) {
        self.attach_shared_mmio(Arc::new(mmio))
    }

    pub fn attach_shared_mmio(&mut self, mmio: Arc<dyn MmioDevice + Sync>) {
        self.mmio.push(mmio);
    }

    fn access_blocking<
        F: FnMut(&(dyn MmioDevice + Sync), LeU64) -> Result<(), CacheAccessError>,
    >(
        mut f: F,
        dev: &(dyn MmioDevice + Sync),
        addr: LeU64,
    ) -> Result<(), CacheAccessError> {
        for i in 0..128 {
            match f(dev, addr) {
                Ok(()) => return Ok(()),
                Err(CacheAccessError::Locked) => {
                    if i < 16 {
                        core::hint::spin_loop()
                    } else {
                        std::thread::yield_now()
                    }
                }
                Err(e) => return Err(e),
            }
        }
        loop {
            match f(dev, addr) {
                Ok(()) => return Ok(()),
                Err(CacheAccessError::Locked) => dev.park_on_unlock(),
                Err(e) => return Err(e),
            }
        }
    }

    pub fn read(&self, addr: LeU64, data: &mut [u8]) -> Result<(), CacheAccessError> {
        for dev in &self.mmio {
            if dev.responds_to_addr(addr)? {
                match Self::access_blocking(|dev, addr| dev.read(addr, data), &**dev, addr) {
                    Ok(()) => return Ok(()),
                    Err(CacheAccessError::NotPresent) => continue,
                    Err(e) => return Err(e),
                }
            }
        }

        Err(CacheAccessError::NotPresent)
    }

    pub fn write(&self, addr: LeU64, data: &[u8]) -> Result<(), CacheAccessError> {
        for dev in &self.mmio {
            if dev.responds_to_addr(addr)? {
                match Self::access_blocking(|dev, addr| dev.write(addr, data), &**dev, addr) {
                    Ok(()) => return Ok(()),
                    Err(CacheAccessError::NotPresent) => continue,
                    Err(e) => return Err(e),
                }
            }
        }

        Err(CacheAccessError::NotPresent)
    }

    pub fn port_out(&self, addr_b: LeU64, data: LeU64, size: SizeControl) {
        for dev in &self.ports {
            if dev.responds_to_port_addr(addr_b) {
                dev.port_out(addr_b, data, size);
                return;
            }
        }
    }

    pub fn port_in(&self, addr_b: LeU64, size: SizeControl) -> LeU64 {
        for dev in &self.ports {
            if dev.responds_to_port_addr(addr_b) {
                return dev.port_in(addr_b, size);
            }
        }
        LeU64::new(0)
    }
}
