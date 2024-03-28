use clever_emu_primitives::bitfield;

use clever_emu_primitives::primitive::*;

use clever_emu_types::CheckModeError;
use clever_emu_types::{CheckValidError, ExecutionMode};

impl From<CheckValidError> for CPUException {
    fn from(_: CheckValidError) -> Self {
        Self::Undefined
    }
}

impl From<CheckModeError> for CPUException {
    fn from(_: CheckModeError) -> Self {
        Self::SystemProtection(LeU64::new(0))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CPUException {
    Abort,
    Undefined,
    SystemProtection(LeU64),
    PageFault(LeI64, FaultCharacteristics),
    ExecutionAlignment(LeI64),
    NonMaskableInterrupt,
    #[cfg(feature = "float")]
    FloatingPointException(FpException),
    Reset,
}

use bytemuck::{Pod, Zeroable};

#[cfg(feature = "float")]
use clever_emu_primitives::float::FpException;

bitfield! {
    pub struct FaultStatus: LeU16{
        pub mode @ 0..2: ExecutionMode,
        pub validation_error @ 8: bool,
        pub non_canonical @ 9: bool,
        pub non_paged @ 10: bool,
        pub prevented @ 11: bool,
        pub nested @ 12: bool,
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    #[derive(Pod,Zeroable)]
    pub enum AccessKind{
        Access = 0,
        Write = 1,
        Execute = 2,

        Allocate = 0xff
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
#[repr(C, align(16))]
pub struct FaultCharacteristics {
    pub pref: LeU64, // The value page Entry the fault occured at. If cr0.PG=0, this is equal to the page of the fault address
    pub flevel: LeU8, // The level of the page table that the fault occured on.
    pub access_kind: AccessKind,
    pub status: FaultStatus,
    #[doc(hidden)]
    pub __reserved: [LeU16; 2],
}

pub type CPUResult<T> = std::result::Result<T, CPUException>;
