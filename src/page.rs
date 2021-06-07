use bytemuck::{Pod, Zeroable};

use crate::error::{AccessKind, CPUException, CPUResult, FaultCharacteristics};

#[derive(Copy, Clone, Zeroable, Pod)]
#[repr(transparent)]
pub struct PageEntry(pub u64);

bitflags::bitflags! {

    pub struct PageFlags: u64{
        const PRESENT = 0b01;
        const WRITABLE = 0b010;
        const NX = 0b0100;
        const XM = 0b01000;
        const SXP = 0b010000;
        const OSSU0 = 0b01000000000;
        const OSSU1 = 0b010000000000;
        const OSSU2 = 0b0100000000000;
        const OSSU3 = 0b1000000000000;
    }
}

impl PageEntry {
    pub fn get_flags(&self) -> PageFlags {
        PageFlags::from_bits_truncate(self.0 & 0xfff)
    }

    pub fn get_value(&self) -> u64 {
        self.0 & !0xfff
    }

    pub fn check_access(&self, access: AccessKind, level: u8, vaddr: i64) -> CPUResult<()> {
        let flags = self.get_flags();
        if flags.bits() != (self.0 & 0xfff) {
            return Err(CPUException::PageFault(
                vaddr,
                FaultCharacteristics {
                    pref: self.get_value() as i64,
                    flevel: level,
                    access_kind: access,
                    ..Zeroable::zeroed()
                },
            ));
        }
        if !match access {
            AccessKind::Write => flags.contains(PageFlags::WRITABLE | PageFlags::PRESENT),
            AccessKind::Execute => {
                flags.contains(PageFlags::PRESENT) && !flags.contains(PageFlags::NX)
            }
            _ => flags.contains(PageFlags::PRESENT),
        } {
            Err(CPUException::PageFault(
                vaddr,
                FaultCharacteristics {
                    pref: self.get_value() as i64,
                    flevel: level,
                    access_kind: access,
                    ..Zeroable::zeroed()
                },
            ))
        } else {
            Ok(())
        }
    }
}

#[derive(Copy, Clone)]
#[repr(C, align(4096))]
pub struct LevelPageTable(pub [PageEntry; 512]);
