use clever_emu_primitives::{bitfield::*, le_fake_enum, primitive::*};
use clever_emu_regs::*;
use clever_emu_types::{CleverRegister, ShiftSizeControl, SizeControl};
use paste::paste;

macro_rules! def_enum{
    {
        #[repr($base_ty:ident)]
        $vis:vis enum $gname:ident @ $opcstart:literal .. $opcend:literal {
            $($(#[$meta:meta])* $uop:ident {$($decode_bits:tt)*} = $uopc:literal),* $(,)?
        }
    } => {
        paste!{
            $vis mod [<$gname:snake _bits>]{
                use super::*;
                $(::clever_emu_primitives::bitfield::bitfield!{
                    $(#[$meta])*
                    pub struct $uop : $base_ty{
                        $($decode_bits)*
                    }
                })*
            }

            bitfield!{
                $vis struct [<$gname Encoded>]: $base_ty{
                    $vis decodebits @ 0..$opcstart : $base_ty,
                    $vis discrim @ $opcstart .. $opcend : LeU8,
                }
            }

            #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
            $vis enum $gname{
                $($(#[$meta])* $uop ([<$gname:snake _bits>]::$uop),)*
            }

            impl [<$gname Encoded>]{
                $vis fn decode(self) -> Option<$gname>{
                    match self.discrim().get(){
                        $($(#[$meta])* $uopc => Some($gname :: $uop ( [<$gname:snake _bits>]::$uop::from_bits(self.decodebits()))),)*
                        _ => None
                    }
                }
            }
        }
    }
}

def_enum! {
    #[repr(BeU16)]
    pub enum Operand @ 14..16{
        Register {vec @ 13 : bool, ss @ 8..11: SizeControl, reg @ 0..8: CleverRegister} = 0,
        Indirect {off @ 9..13: CleverRegister, scale @ 7..9: LeU8, ss @ 4..7: SizeControl, base @ 0..8: CleverRegister} = 1,
        ImmShort {rel @ 12: bool, imm @ 0..12: LeU16} = 2,
        ImmLong { mem @ 13: bool, rel @ 10: bool, immss @ 8..10: ShiftSizeControl, memss @ 4..6: SizeControl, dispreg @ 0..4: CleverRegister} = 3,
    }
}

def_enum! {
    #[repr(BeU16)]
    pub enum NonBranchOpcode @ 4..16{
        Und{} = 0,
        Add {lock @ 3: bool, supress_flags @ 0: bool} = 1,
        Sub {lock @ 3: bool, supress_flags @ 0: bool} = 2,
        And {lock @ 3: bool, supress_flags @ 0: bool} = 3,
        Or  {lock @ 3: bool, supress_flags @ 0: bool} = 4,
        Xor {lock @ 3: bool, supress_flags @ 0: bool} = 5,

    }
}
