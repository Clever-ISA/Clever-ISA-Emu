#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CPUException {
    Abort,
    Undefined,
    SystemProtection(u64),
    PageFault(i64, FaultCharacteristics),
    ExecutionAlignment(i64),
    NonMaskableInterrupt,

    Reset,
}

use bytemuck::{Pod, Zeroable};

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

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
#[repr(C, align(16))]
pub struct FaultCharacteristics {
    pub pref: i64, // The value page Entry the fault occured at. If cr0.PG=0, this is equal to the page of the fault address
    pub flevel: u8, // The level of the page table that the fault occured on.
    pub access_kind: AccessKind,
    #[doc(hidden)]
    pub __reserved: [u16; 3],
}

pub type CPUResult<T> = std::result::Result<T, CPUException>;
