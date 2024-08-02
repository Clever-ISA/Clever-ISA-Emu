use clever_emu_primitives::{bitfield, le_fake_enum, primitive::*};
use clever_emu_types::ExecutionMode;

bitfield! {
    pub struct PageEntry : LeU64{
        pub perm @ 0..2 : LeU8,
        pub xm @ 2..4 : ExecutionMode,
        pub supervisor_use @ 9..12 : LeU16,
        pub addr @ 12..64 : LeU64,
    }
}

impl PageEntry {
    pub fn npe_perm(&self) -> NpePermission {
        NpePermission(self.perm())
    }
    pub fn lpe_perm(&self) -> LpePermission {
        LpePermission(self.perm())
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    pub enum LpePermission {
        Empty = 0,
        Read = 1,
        Write = 2,
        Exec = 3,
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    pub enum NpePermission{
        Empty = 0,
        Avail = 1,
    }
}
