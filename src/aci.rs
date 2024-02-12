use std::rc::Rc;

use crate::primitive::*;

pub trait AciDevice {
    fn dma_write(&self, devid: LeU16, dma_addr: LeU16, val: LeU32);
    fn dma_read(&self, devid: LeU16, dma_addr: LeU16, val: LeU32);
    fn interrupt_raised(&self) -> bool;
}

pub struct AciBridge {
    bridged: Vec<Rc<dyn AciDevice>>,
}
