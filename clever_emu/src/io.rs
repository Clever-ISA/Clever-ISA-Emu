use crate::cpu::SizeControl;
use crate::primitive::*;

pub trait IOPort {
    fn matches(&self, addr: LeU64) -> bool;
    fn read(&self, addr: LeU64, size: SizeControl) -> LeU64;
    fn write(&self, addr: LeU64, val: LeU64, size: SizeControl);
}

pub trait MMIODevice {
    fn requires_align(&self) -> bool {
        true
    }
    fn matches(&self, addr: LeU64) -> bool;
    fn read(&self, addr: LeU64, size: SizeControl) -> LeU64;
    fn write(&self, addr: LeU64, val: LeU64, size: SizeControl);
}
