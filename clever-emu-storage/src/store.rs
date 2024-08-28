#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum StorageMode {
    ReadOnly,
    ReadWrite,
}

pub trait Storage {
    fn mode(&self) -> StorageMode;
}
