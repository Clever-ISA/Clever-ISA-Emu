use std::{
    fs::{self, OpenOptions},
    io::{self, Read as _, Seek as _, Write as _},
    path::Path,
    rc::Rc,
    sync::Arc,
};

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum StorageMode {
    ReadOnly,
    ReadWrite,
}

impl StorageMode {
    pub fn to_open_options(&self) -> OpenOptions {
        let mut options = OpenOptions::new();
        options.read(true);
        if let StorageMode::ReadWrite = self {
            options.write(true);
        }
        options
    }
}

pub trait Storage {
    fn mode(&self) -> StorageMode;
    fn max_size(&self) -> u64;

    fn read_storage(&self, addr: u64, buf: &mut [u8]) -> io::Result<()>;
    fn write_storage(&self, addr: u64, buf: &[u8]) -> io::Result<()>;
}

impl<T: Storage + ?Sized> Storage for &T {
    fn max_size(&self) -> u64 {
        T::max_size(self)
    }
    fn mode(&self) -> StorageMode {
        T::mode(self)
    }
    fn read_storage(&self, addr: u64, buf: &mut [u8]) -> io::Result<()> {
        T::read_storage(self, addr, buf)
    }
    fn write_storage(&self, addr: u64, buf: &[u8]) -> io::Result<()> {
        T::write_storage(self, addr, buf)
    }
}

impl<T: Storage + ?Sized> Storage for &mut T {
    fn max_size(&self) -> u64 {
        T::max_size(self)
    }
    fn mode(&self) -> StorageMode {
        T::mode(self)
    }
    fn read_storage(&self, addr: u64, buf: &mut [u8]) -> io::Result<()> {
        T::read_storage(self, addr, buf)
    }
    fn write_storage(&self, addr: u64, buf: &[u8]) -> io::Result<()> {
        T::write_storage(self, addr, buf)
    }
}

impl<T: Storage + ?Sized> Storage for Arc<T> {
    fn max_size(&self) -> u64 {
        T::max_size(self)
    }
    fn mode(&self) -> StorageMode {
        T::mode(self)
    }
    fn read_storage(&self, addr: u64, buf: &mut [u8]) -> io::Result<()> {
        T::read_storage(self, addr, buf)
    }
    fn write_storage(&self, addr: u64, buf: &[u8]) -> io::Result<()> {
        T::write_storage(self, addr, buf)
    }
}

impl<T: Storage + ?Sized> Storage for Rc<T> {
    fn max_size(&self) -> u64 {
        T::max_size(self)
    }
    fn mode(&self) -> StorageMode {
        T::mode(self)
    }
    fn read_storage(&self, addr: u64, buf: &mut [u8]) -> io::Result<()> {
        T::read_storage(self, addr, buf)
    }
    fn write_storage(&self, addr: u64, buf: &[u8]) -> io::Result<()> {
        T::write_storage(self, addr, buf)
    }
}

impl<T: Storage + ?Sized> Storage for Box<T> {
    fn max_size(&self) -> u64 {
        T::max_size(self)
    }
    fn mode(&self) -> StorageMode {
        T::mode(self)
    }
    fn read_storage(&self, addr: u64, buf: &mut [u8]) -> io::Result<()> {
        T::read_storage(self, addr, buf)
    }
    fn write_storage(&self, addr: u64, buf: &[u8]) -> io::Result<()> {
        T::write_storage(self, addr, buf)
    }
}

#[derive(Debug)]
pub struct DirectStorage(fs::File, StorageMode, u64);

impl DirectStorage {
    pub fn open(path: &Path, mode: StorageMode) -> io::Result<Self> {
        mode.to_open_options().open(path).map(|file| {
            let len = (&file).seek(io::SeekFrom::End(0)).unwrap_or(0);
            DirectStorage(file, mode, len)
        })
    }
}

impl io::Read for DirectStorage {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }
}

impl io::Read for &DirectStorage {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        (&self.0).read(buf)
    }
}

impl io::Write for DirectStorage {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
}

impl io::Write for &DirectStorage {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        (&self.0).write(buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        (&self.0).flush()
    }
}

impl io::Seek for DirectStorage {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        self.0.seek(pos)
    }
}

impl io::Seek for &DirectStorage {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        (&self.0).seek(pos)
    }
}

impl Storage for DirectStorage {
    fn mode(&self) -> StorageMode {
        self.1
    }

    fn max_size(&self) -> u64 {
        self.2
    }

    fn read_storage(mut self: &Self, addr: u64, buf: &mut [u8]) -> io::Result<()> {
        self.seek(io::SeekFrom::Start(addr))?;
        self.read_exact(buf)
    }

    fn write_storage(mut self: &Self, addr: u64, buf: &[u8]) -> io::Result<()> {
        self.seek(io::SeekFrom::Start(addr))?;
        self.write_all(buf)
    }
}
