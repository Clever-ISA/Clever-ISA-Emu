use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

use parking_lot::{RwLock, RwLockWriteGuard};

pub trait IOPort {
    fn matches_addr(&self, addr: u64) -> bool;
    fn read(&mut self, size: u64) -> u64 {
        0
    }
    fn write(&mut self, size: u64, val: u64) {}
}

#[derive(Clone)]
pub struct IOBus {
    devices: Vec<Arc<RwLock<dyn IOPort>>>,
}

pub struct IOGuard<'a>(RwLockWriteGuard<'a, dyn IOPort>);

impl Deref for IOGuard<'_> {
    type Target = dyn IOPort;
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl DerefMut for IOGuard<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.0
    }
}

impl IOBus {
    pub const fn new() -> Self {
        Self {
            devices: Vec::new(),
        }
    }
    pub fn register<I: IOPort + 'static>(&mut self, dev: I) {
        self.devices.push(Arc::new(RwLock::new(dev)))
    }
    pub fn get_port_for_addr(&self, addr: u64) -> Option<IOGuard> {
        for dev in &self.devices {
            let read_lock = dev.read();
            if read_lock.matches_addr(addr) {
                drop(read_lock);
                return Some(IOGuard(dev.write()));
            }
        }
        None
    }
}
