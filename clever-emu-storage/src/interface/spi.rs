use clever_emu_mem::io::IoPort;
use clever_emu_primitives::primitive::LeU64;
use core::sync::atomic::{AtomicU8, Ordering};

pub trait SpiDevice {
    fn transfer(&self, in_data: u8) -> u8;
}

pub struct SpiController {
    devices: Vec<Box<dyn SpiDevice + Sync>>,
    cs: AtomicU8,
    last_val: AtomicU8,
}

impl Default for SpiController {
    fn default() -> Self {
        Self::new()
    }
}

impl SpiController {
    pub const fn new() -> Self {
        Self {
            devices: Vec::new(),
            cs: AtomicU8::new(!0),
            last_val: AtomicU8::new(0),
        }
    }

    pub fn attach_dyn(&mut self, dev: Box<dyn SpiDevice + Sync + 'static>) {
        if u8::try_from(self.devices.len()).is_err() {
            panic!("Cannot attach more than 256 spi devices");
        }
        self.devices.push(dev);
    }
    pub fn attach<T: SpiDevice + Sync + 'static>(&mut self, dev: T) {
        self.attach_dyn(Box::new(dev))
    }
}

impl IoPort for SpiController {
    fn responds_to_port_addr(&self, addr: LeU64) -> bool {
        (LeU64::new(0x7f000020)..LeU64::new(0x7f000023)).contains(&addr)
    }

    fn port_in(&self, addr: LeU64, size: clever_emu_types::SizeControl) -> LeU64 {
        match addr.get() {
            0x72000020 => LeU64::new(self.devices.len() as u64),
            0x72000021 => LeU64::new(self.cs.load(Ordering::Relaxed) as u64),
            0x72000022 => LeU64::new(self.last_val.load(Ordering::Relaxed) as u64),
            _ => LeU64::new(0),
        }
    }

    fn port_out(&self, addr: LeU64, data: LeU64, _: clever_emu_types::SizeControl) {
        match addr.get() {
            0x72000021 => {
                let byte = (data & 0xFF).get() as u8;
                self.cs.store(byte, Ordering::Relaxed);
            }
            0x72000022 => {
                let byte = (data & 0xFF).get() as u8;

                let devno = self.cs.load(Ordering::Relaxed) as usize;
                let Some(device) = self.devices.get(devno) else {
                    self.last_val.store(0, Ordering::Relaxed);
                    return;
                };
                self.last_val
                    .store(device.transfer(byte), Ordering::Relaxed);
            }
            _ => {}
        }
    }
}
