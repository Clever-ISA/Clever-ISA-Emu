#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CPUException {
    Abort,
    Undefined,
    SystemProtection(u64),
    PageFault(i64, FaultCharacteristics),
    ExecutionAlignment(i64),
    NonMaskableInterrupt,
    FloatingPointException(FpException),
    Reset,
}

use bytemuck::{Pod, Zeroable};

use crate::float::FpException;

fake_enum::fake_enum! {
    #[repr(u8)]
    #[derive(Pod,Zeroable, Hash)]
    pub enum struct AccessKind{
        Access = 0,
        Write = 1,
        Execute = 2,

        Allocate = 0xff
    }
}

bitflags::bitflags! {
    #[derive(Zeroable, Pod)]
    #[repr(transparent)]
    pub struct FaultStatus : u16{
        const STATUS_XM = 0x0001;
        const STATUS_XMM = 0x0002;
        const STATUS_VALIDATION_ERROR = 0x0100;
        const STATUS_NON_CANONICAL = 0x0200;
        const STATUS_NON_PAGED = 0x0400;
        const STATUS_PREVENTED = 0x0800;
        const STATUS_NESTED = 0x1000;
    }
}

impl FaultStatus {
    pub const STATUS_USER: Self = Self { bits: 0x0003 };
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
#[repr(C, align(16))]
pub struct FaultCharacteristics {
    pub pref: u64, // The value page Entry the fault occured at. If cr0.PG=0, this is equal to the page of the fault address
    pub flevel: u8, // The level of the page table that the fault occured on.
    pub access_kind: AccessKind,
    pub status: FaultStatus,
    #[doc(hidden)]
    pub __reserved: [u16; 2],
}

pub type CPUResult<T> = std::result::Result<T, CPUException>;
