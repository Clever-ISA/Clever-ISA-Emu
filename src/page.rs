use bytemuck::{Pod, Zeroable};

use crate::{
    cpu::CpuExecutionMode,
    error::{AccessKind, CPUException, CPUResult, FaultCharacteristics, FaultStatus},
};

#[derive(Copy, Clone, Zeroable, Pod)]
#[repr(transparent)]
pub struct PageEntry(pub u64);

#[repr(u64)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum LowerPagePermission {
    Empty = 0,
    Read = 1,
    Write = 2,
    Exec = 3,
}

unsafe impl Zeroable for LowerPagePermission {}

#[repr(u64)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum NestedPagePermission {
    Empty = 0,
    Present = 1,
}

unsafe impl Zeroable for NestedPagePermission {}

bitflags::bitflags! {
    pub struct PageFlags: u64{
        const XM  = 0b000100;
        const XMM = 0b001000;
        const SXP = 0b010000;
        const OSSU0 = 0b01000000000;
        const OSSU1 = 0b010000000000;
        const OSSU2 = 0b0100000000000;
        const OSSU3 = 0b1000000000000;
    }
}

impl PageEntry {
    pub fn lower_page_permission(&self) -> LowerPagePermission {
        // SAFETY:
        // All discriminants from 0 to 3 are populated
        unsafe { core::mem::transmute(self.0 & 0x3) }
    }

    pub fn nested_page_permission(&self) -> Option<NestedPagePermission> {
        match self.0 & 0x3 {
            2 | 3 => None,
            x => Some(unsafe { core::mem::transmute(x) }),
        }
    }

    pub fn flags(&self) -> PageFlags {
        PageFlags::from_bits_truncate(self.0 & 0xffc)
    }

    pub fn value(&self) -> u64 {
        self.0 & !0xfff
    }

    pub fn check_access(
        &self,
        access: AccessKind,
        level: u8,
        vaddr: i64,
        mode: CpuExecutionMode,
    ) -> CPUResult<()> {
        let base_status = match mode {
            CpuExecutionMode::Supervisor => FaultStatus::empty(),
            CpuExecutionMode::User => FaultStatus::STATUS_USER,
        } | if level > 0 {
            FaultStatus::STATUS_NESTED
        } else {
            FaultStatus::empty()
        };
        let flags = self.flags();

        if flags.bits() != self.0 & 0xffc {
            return Err(CPUException::PageFault(
                vaddr,
                FaultCharacteristics {
                    pref: self.0,
                    access_kind: access,
                    flevel: level,
                    status: base_status | FaultStatus::STATUS_VALIDATION_ERROR,
                    ..Zeroable::zeroed()
                },
            ));
        }

        if flags.contains(PageFlags::XM) ^ flags.contains(PageFlags::XMM) {
            return Err(CPUException::PageFault(
                vaddr,
                FaultCharacteristics {
                    pref: self.0,
                    access_kind: access,
                    flevel: level,
                    status: base_status | FaultStatus::STATUS_VALIDATION_ERROR,
                    ..Zeroable::zeroed()
                },
            ));
        }

        if flags.contains(PageFlags::SXP)
            && access == AccessKind::Execute
            && mode == CpuExecutionMode::Supervisor
        {
            return Err(CPUException::PageFault(
                vaddr,
                FaultCharacteristics {
                    pref: self.0,
                    access_kind: access,
                    flevel: level,
                    status: base_status | FaultStatus::STATUS_PREVENTED,
                    ..Zeroable::zeroed()
                },
            ));
        }

        if !flags.contains(PageFlags::XM) && mode == CpuExecutionMode::User {
            return Err(CPUException::PageFault(
                vaddr,
                FaultCharacteristics {
                    pref: self.0,
                    access_kind: access,
                    flevel: level,
                    status: base_status,
                    ..Zeroable::zeroed()
                },
            ));
        }

        if level > 0 {
            match self.nested_page_permission().ok_or_else(|| {
                CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        pref: self.0,
                        access_kind: access,
                        flevel: level,
                        status: base_status | FaultStatus::STATUS_VALIDATION_ERROR,
                        ..Zeroable::zeroed()
                    },
                )
            })? {
                NestedPagePermission::Empty => Err(CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        pref: self.0,
                        access_kind: access,
                        flevel: level,
                        status: base_status,
                        ..Zeroable::zeroed()
                    },
                )),
                NestedPagePermission::Present => Ok(()),
            }
        } else {
            match (self.lower_page_permission(), access) {
                (LowerPagePermission::Empty, _) => Err(CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        pref: self.0,
                        access_kind: access,
                        flevel: level,
                        status: base_status,
                        ..Zeroable::zeroed()
                    },
                )),
                (_, AccessKind::Access) => Ok(()),
                (LowerPagePermission::Write, AccessKind::Write) => Ok(()),
                (LowerPagePermission::Exec, AccessKind::Execute) => Ok(()),
                _ => Err(CPUException::PageFault(
                    vaddr,
                    FaultCharacteristics {
                        pref: self.0,
                        access_kind: access,
                        flevel: level,
                        status: base_status,
                        ..Zeroable::zeroed()
                    },
                )),
            }
        }
    }
}

#[derive(Copy, Clone)]
#[repr(C, align(4096))]
pub struct LevelPageTable(pub [PageEntry; 512]);
