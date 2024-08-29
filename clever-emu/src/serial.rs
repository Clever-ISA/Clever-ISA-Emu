use clever_emu_mem::io::IoPort;
use clever_emu_storage::store::StorageMode;
use std::{
    fs::{File, OpenOptions},
    io::{self, Read, Write},
    path::Path,
};

use clever_emu_types::SizeControl;

use clever_emu_primitives::primitive::LeU64;

enum SerialObject {
    File(File),
    Tty,
}

pub struct SerialDevice(SerialObject);

impl SerialDevice {
    pub fn open(path: &Path, mode: StorageMode) -> io::Result<Self> {
        mode.to_open_options()
            .open(path)
            .map(|file| SerialDevice(SerialObject::File(file)))
    }

    pub fn open_tty() -> io::Result<SerialDevice> {
        Ok(Self(SerialObject::Tty))
    }
}

impl IoPort for SerialDevice {
    fn responds_to_port_addr(&self, addr: LeU64) -> bool {
        addr == LeU64::new(0x100000000)
    }
    fn port_in(&self, _: LeU64, size: SizeControl) -> LeU64 {
        let len = size.as_bytes();

        let mut val = LeU64::new(0);
        // There's no good way to yield an error from an I/O Port, but yielding 0 is fine*
        // if a complete error occurs, then we get all zeros.
        match &self.0 {
            SerialObject::File(f) => {
                let mut f = f;
                let _ = f.read_exact(&mut bytemuck::bytes_of_mut(&mut val)[..len]);
            }
            SerialObject::Tty => {
                let _ = std::io::stdin().read_exact(&mut bytemuck::bytes_of_mut(&mut val)[..len]);
            }
        }

        val
    }

    fn port_out(&self, _: LeU64, data: LeU64, size: SizeControl) {
        let len = size.as_bytes();

        // There's no good way to yield an error from an I/O Port, but yielding 0 is fine*
        match &self.0 {
            SerialObject::File(f) => {
                let mut f = f;

                let _ = f.write_all(&bytemuck::bytes_of(&data)[..len]);
            }
            SerialObject::Tty => {
                let _ = std::io::stdout().write_all(&bytemuck::bytes_of(&data)[..len]);
            }
        }
    }
}
