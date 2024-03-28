use crate::cpu::CpuExecutionMode;
use crate::cpu::ExecutionMode;
use crate::error::AccessKind;
use crate::error::CPUException;
use crate::error::CPUResult;
use crate::error::FaultCharacteristics;
use crate::error::FaultStatus;
use crate::primitive::*;

use crate::bitfield;

le_fake_enum! {
    #[repr(LeU8)]
    #[derive(bytemuck::Pod, bytemuck::Zeroable)]
    pub enum LpePerm{
        Empty = 0,
        Read = 1,
        Write = 2,
        Exec = 3
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    #[derive(bytemuck::Pod, bytemuck::Zeroable)]
    pub enum NpePerm{
        Empty = 0,
        Present = 1,
    }
}

bitfield! {
    pub struct LpeBits: LeU16{
        pub perm @ 0..2: LpePerm,
        pub xm @ 2..4: ExecutionMode,
        pub sxp @ 4: bool,
        pub supervisor @ 10..12: LeU16,
    }
}

impl LpeBits {
    pub fn check_valid(&self, vaddr: LeI64, mut rest_fault: FaultCharacteristics) -> CPUResult<()> {
        rest_fault.status |= FaultStatus::with_validation_error(true);
        if self.validate() {
            Err(CPUException::PageFault(vaddr, rest_fault))
        } else {
            match self.xm().check_valid() {
                Ok(()) => Ok(()),
                Err(_) => Err(CPUException::PageFault(vaddr, rest_fault)),
            }
        }
    }
}

bitfield! {
    pub struct NpeBits: LeU16{
        pub perm @ 0..1: NpePerm,
        pub xm @ 2..4: ExecutionMode,
        pub sxp @ 4: bool,
        pub supervisor @ 10..12: LeU16,
    }
}

impl NpeBits {
    pub fn check_valid(&self, vaddr: LeI64, mut rest_fault: FaultCharacteristics) -> CPUResult<()> {
        rest_fault.status |= FaultStatus::with_validation_error(true);
        if self.validate() {
            Err(CPUException::PageFault(vaddr, rest_fault))
        } else {
            match self.xm().check_valid() {
                Ok(()) => Ok(()),
                Err(_) => Err(CPUException::PageFault(vaddr, rest_fault)),
            }
        }
    }
}

bitfield! {
    pub struct SharedBits: LeU16{
        pub perm @ 0..2: LeU8,
        pub xm @ 2..4: ExecutionMode,
        pub sxp @ 4: bool,
        pub supervisor @ 10..12: LeU16,
    }
}

bitfield! {
    pub struct PageEntry : LeU64{
        pub flags @ 0..12: SharedBits,
        pub addr @ 12..64: LeU64
    }
}

impl PageEntry {
    pub fn lpe_flags(self) -> LpeBits {
        LpeBits::from_bits(self.flags().bits())
    }

    pub fn npe_flags(self) -> NpeBits {
        NpeBits::from_bits(self.flags().bits())
    }

    pub fn page_addr(self) -> LeU64 {
        self.addr() << 12
    }

    pub fn try_access(
        self,
        level: LeU8,
        mode: CpuExecutionMode,
        access: AccessKind,
        mut rest_fault_info: FaultCharacteristics,
        vaddr: LeI64,
    ) -> CPUResult<()> {
        rest_fault_info.status |= FaultStatus::with_mode(ExecutionMode::from_mode(mode));

        rest_fault_info.access_kind = access;
        rest_fault_info.pref = self.page_addr();
        rest_fault_info.flevel = level;

        if !self.flags().validate() {
            return Err(CPUException::PageFault(vaddr, rest_fault_info));
        }

        if mode > self.flags().xm().mode() {
            return Err(CPUException::PageFault(vaddr, rest_fault_info));
        }

        if level == 0 {
            self.lpe_flags().check_valid(vaddr, rest_fault_info)?;

            match (access, self.lpe_flags().perm()) {
                (_, LpePerm::Empty) => Err(CPUException::PageFault(vaddr, rest_fault_info)),
                (AccessKind::Access, _) | (AccessKind::Write, LpePerm::Write) => Ok(()),
                (AccessKind::Execute, LpePerm::Exec) => {
                    if self.lpe_flags().sxp() && mode == CpuExecutionMode::Supervisor {
                        rest_fault_info.status |= FaultStatus::with_prevented(true);
                        Err(CPUException::PageFault(vaddr, rest_fault_info))
                    } else {
                        Ok(())
                    }
                }
                _ => Err(CPUException::PageFault(vaddr, rest_fault_info)),
            }
        } else {
            self.npe_flags().check_valid(vaddr, rest_fault_info)?;

            if self.npe_flags().perm() == NpePerm::Empty {
                Err(CPUException::PageFault(vaddr, rest_fault_info))
            } else if access == AccessKind::Execute
                && self.lpe_flags().sxp()
                && mode == CpuExecutionMode::Supervisor
            {
                rest_fault_info.status |= FaultStatus::with_prevented(true);
                Err(CPUException::PageFault(vaddr, rest_fault_info))
            } else {
                Ok(())
            }
        }
    }
}
