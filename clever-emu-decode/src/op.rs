use clever_emu_primitives::{bitfield, bitfield::*, le_fake_enum, primitive::*};
use clever_emu_regs::*;
use clever_emu_types::{CleverRegister, ShiftSizeControl, SizeControl};
use paste::paste;

#[cfg(feature = "float")]
use clever_emu_primitives::float::RoundingMode;

macro_rules! def_enum{
    {
        #[repr($base_ty:ident)]
        $(#[$outer_meta:meta])*
        $vis:vis enum $gname:ident @ $(#[$opcode_meta:meta])* $opcstart:literal .. $opcend:literal {
            $(#![$enum_meta:meta])*
            $($(#[$meta:meta])* $uop:ident {$($decode_bits:tt)*} = $uopc:literal),* $(,)?
        }
    } => {
        paste!{
            $(#[$outer_meta])*
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
                $(#[$outer_meta])*
                $vis struct [<$gname Encoded>]: $base_ty{
                    $vis decodebits @ 0..$opcstart : $base_ty,
                    $(#[$opcode_meta])*
                    $vis discrim @ $opcstart .. $opcend : $base_ty,
                }
            }

            #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
            $(#[$outer_meta])*
            $(#[$enum_meta])*
            $vis enum $gname{
                $($(#[$meta])* $uop ([<$gname:snake _bits>]::$uop),)*

                #[doc(hidden)]
                __Invalid([<$gname Encoded>])
            }

            $(#[$outer_meta])*
            impl $gname{
                $vis fn encode(self) -> [<$gname Encoded>]{
                    match self{
                        $($(#[$meta])* Self:: $uop(payload) => [<$gname Encoded>]::with_discrim(<$base_ty>::new($uopc)).insert_decodebits(payload.to_bits()),)*
                        Self::__Invalid(payload) => payload,
                    }
                }

            }

            $(#[$outer_meta])*
            impl<R: ::clever_emu_primitives::bitfield::BitfieldTy> ::clever_emu_primitives::bitfield::FromBitfield<R> for $gname where [<$gname Encoded>]: ::clever_emu_primitives::bitfield::FromBitfield<R>{
                fn validate(self) -> bool{
                    match self{
                        $($(#[$meta])* Self:: $uop(payload) => payload.validate(),)*
                        Self::__Invalid(_) => false
                    }
                }

                fn from_bits(bits: R) -> Self{
                    <[<$gname Encoded>] as ::clever_emu_primitives::bitfield::FromBitfield::<R>>::from_bits(bits).decode()
                }

                fn to_bits(self) -> R{
                    <[<$gname Encoded>] as ::clever_emu_primitives::bitfield::FromBitfield::<R>>::to_bits(self.encode())
                }
            }


            $(#[$outer_meta])*
            impl ::clever_emu_primitives::bitfield::DisplayBitfield for $gname{
                fn present(&self) -> bool{
                    true
                }

                fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result{
                    f.write_str(name)?;
                    f.write_str(": ")?;
                    ::core::fmt::Display::fmt(self, f)
                }
            }

            $(#[$outer_meta])*
            impl ::core::fmt::Display for $gname{
                fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                    match self{
                        $(Self:: $uop (payload) => {
                            f.write_str(::core::stringify!($uop))?;
                            payload.fmt(f)
                        },)*
                        Self::__Invalid(payload) => {
                            f.write_fmt(format_args!("**invalid {}: {:#x}**", ::core::stringify!([<$gname:snake>]), payload.bits()))
                        }
                    }
                }
            }


            $(#[$outer_meta])*
            impl [<$gname Encoded>]{
                $vis fn decode(self) -> $gname{
                    match self.discrim().get(){
                        $($(#[$meta])* $uopc => $gname :: $uop ( [<$gname:snake _bits>]::$uop::from_bits(self.decodebits())),)*
                        __inval => $gname::__Invalid(self)
                    }
                }
            }
        }
    }
}

def_enum! {
    #[repr(BeU16)]
    pub enum InvalidEncoding @ 0..16{}
}

def_enum! {
    #[repr(BeU16)]
    pub enum Operand @ 14..16{
        Register { #[cfg(feature = "vector")] vec @ 13 : bool, ss @ 8..11: SizeControl, reg @ 0..8: CleverRegister} = 0,
        Indirect {off @ 9..13: CleverRegister, scale @ 7..9: LeU8, ss @ 4..7: SizeControl, base @ 0..8: CleverRegister} = 1,
        ImmShort {rel @ 12: bool, imm @ 0..12: LeU16} = 2,
        ImmLong { mem @ 13: bool, rel @ 10: bool, immss @ 8..10: ShiftSizeControl, memss @ 4..6: SizeControl, dispreg @ 0..4: CleverRegister} = 3,
    }
}

le_fake_enum! {
    #[repr(BeU8)]
    pub enum AluOp {
        Nop = 0,
        Add = 1,
        Sub = 2,
        And = 3,
        Or = 4,
        Xor = 5,
    }
}

def_enum! {
    #[repr(BeU16)]
    pub enum NonBranchOpcode @ 4..16{
        #![non_exhaustive]
        Und{} = 0o0000,
        Add {lock @ 3: bool, supress_flags @ 0: bool} = 0o0001,
        Sub {lock @ 3: bool, supress_flags @ 0: bool} = 0o0002,
        And {lock @ 3: bool, supress_flags @ 0: bool} = 0o0003,
        Or  {lock @ 3: bool, supress_flags @ 0: bool} = 0o0004,
        Xor {lock @ 3: bool, supress_flags @ 0: bool} = 0o0005,
        Mul {size @ 2..4: SizeControl, supress_flags @ 0: bool} = 0o0006,
        Div {size @ 2..4: SizeControl, wide @ 1: bool, supress_flags @ 0: bool} = 0o0007,

        Mov {} = 0o0010,
        Lea {} = 0o0011,
        MovGpDst { dst @ 0..4 : CleverRegister} = 0o0012,
        MovGpSrc { src @ 0..4 : CleverRegister} = 0o0013,
        LeaGpDst {dst @ 0..4 : CleverRegister} = 0o0014,

        Nop0 {any @ 0..4: LeU8} = 0o0020,
        Nop1 {any @ 0..4: LeU8} = 0o0021,
        Nop2 {any @ 0..4: LeU8} = 0o0022,
        Nop3 {any @ 0..4: LeU8} = 0o0023,
        Push {} = 0o0024,
        Pop {} = 0o0025,
        PushGp {reg @ 0..4 : CleverRegister} = 0o0026,
        PopGp {reg @ 0..4: CleverRegister} = 0o0027,

        StoGpr {} = 0o0030,
        StoAr {} = 0o0031,
        RstoGpr {} = 0o0032,
        RstoAr {} = 0o0033,
        PushGpr {} = 0o0034,
        PushAr {} = 0o0035,
        PopGpr {} = 0o0036,
        PopAr {} = 0o0037,

        MosSx {supress_flags @ 0: bool} = 0o0040,
        Bswap {supress_flags @ 0: bool} = 0o0041,
        #[cfg(feature = "float")]
        MovIf {unsigned @ 1: bool, supress_flags @ 0: bool} = 0o0042,
        #[cfg(feature = "float")]
        MovXf {format_size @ 2..4: SizeControl, int @ 1: bool, supress_flags @ 0 : bool} = 0o0043,
        #[cfg(feature = "float")]
        MovFi {unsigned @ 1: bool, supress_flags @ 0: bool} = 0o0044,
        #[cfg(feature = "float")]
        MovFx {format_size @ 2..4: SizeControl, int @ 1: bool, supress_flags @ 0 : bool} = 0o0045,
        #[cfg(feature = "float")]
        CvtF {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0046,


        Lsh {lock @ 3: bool, supress_flags @ 0: bool} = 0o0060,
        Rsh {lock @ 3: bool, supress_flags @ 0: bool} = 0o0061,

        Arsh {lock @ 3: bool, supress_flags @ 0: bool} = 0o0063,
        LshC {lock @ 3: bool, supress_flags @ 0: bool} = 0o0064,
        RshC {lock @ 3: bool, supress_flags @ 0: bool} = 0o0065,
        Lrot {lock @ 3: bool, supress_flags @ 0: bool} = 0o0066,
        Rrot {lock @ 3: bool, supress_flags @ 0: bool} = 0o0067,

        LshGpDest {dst @ 0..4 : CleverRegister} = 0o0070,
        RshGpDest {dst @ 0..4 : CleverRegister} = 0o0071,

        ArshGpDest {dst @ 0..4 : CleverRegister} = 0o0073,
        LshCGpDest {dst @ 0..4 : CleverRegister} = 0o0074,
        RshCGpDest {dst @ 0..4 : CleverRegister} = 0o0075,
        LrotGpDest {dst @ 0..4 : CleverRegister} = 0o0076,
        RrotGpDest {dst @ 0..4 : CleverRegister} = 0o0077,

        Imul {size @ 2..4: SizeControl, supress_flags @ 0: bool} = 0o0100,
        AddGpDest {dst @ 0..4 : CleverRegister} = 0o0101,
        SubGpDest {dst @ 0..4 : CleverRegister} = 0o0102,
        AndGpDest {dst @ 0..4 : CleverRegister} = 0o0103,
        OrGpDest  {dst @ 0..4 : CleverRegister} = 0o0104,
        XorGpDest {dst @ 0..4 : CleverRegister} = 0o0105,
        Bnot {lock @ 3: bool, supress_flags @ 0: bool} = 0o0106,
        Neg {lock @ 3: bool, supress_flags @ 0: bool} = 0o0107,

        Idiv {size @ 2..4: SizeControl, wide @ 1: bool, supress_flags @ 0: bool} = 0o0110,
        AddGpSrc {src @ 0..4 : CleverRegister} = 0o0111,
        SubGpSrc {src @ 0..4 : CleverRegister} = 0o0112,
        AndGpSrc {src @ 0..4 : CleverRegister} = 0o0113,
        OrGpSrc  {src @ 0..4 : CleverRegister} = 0o0114,
        XorGpSrc {src @ 0..4 : CleverRegister} = 0o0115,
        BnotGp {reg @ 0..4: CleverRegister} = 0o0116,
        NegGp {reg @ 0..4: CleverRegister} = 0o0117,

        CmovT {cc @ 0..4: ConditionCode} = 0o0150,
        Cmov {cc @ 0..4: ConditionCode} = 0o0151,

        Cmp {} = 0o0154,
        Test {} = 0o0155,
        CmpGp {reg @ 0..4: CleverRegister} = 0o0156,
        TestGp {reg @ 0..4: CleverRegister} = 0o0157,

        #[cfg(feature = "hash-accel")]
        Pload {} = 0o0160,

        #[cfg(feature = "float")]
        Round {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0400,

        #[cfg(feature = "float")]
        Fabs {supress_flags @ 0: bool} = 0o0403,
        #[cfg(feature = "float")]
        Fneg {supress_flags @ 0: bool} = 0o0404,
        #[cfg(feature = "float")]
        Finv {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0405,
        #[cfg(feature = "float")]
        Fadd {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0406,
        #[cfg(feature = "float")]
        Fsub {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0407,
        #[cfg(feature = "float")]
        Fmul {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0410,
        #[cfg(feature = "float")]
        Fdiv {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0411,
        #[cfg(feature = "float")]
        Frem {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0412,
        #[cfg(feature = "float")]
        Ffma {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0413,
        #[cfg(feature = "float")]
        Fcmpz {} = 0o0430,
        #[cfg(feature = "float")]
        Fcmp {} = 0o0431,
        #[cfg(feature = "float-ext")]
        Exp {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0440,
        #[cfg(feature = "float-ext")]
        Ln {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0441,
        #[cfg(feature = "float-ext")]
        Lg {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0442,
        #[cfg(feature = "float-ext")]
        Sin {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0443,
        #[cfg(feature = "float-ext")]
        Cos {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0444,
        #[cfg(feature = "float-ext")]
        Tan {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0445,
        #[cfg(feature = "float-ext")]
        Asin {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0446,
        #[cfg(feature = "float-ext")]
        Acos {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0447,
        #[cfg(feature = "float-ext")]
        Atan {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0450,
        #[cfg(feature = "float-ext")]
        Exp2 {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0451,
        #[cfg(feature = "float-ext")]
        Log10 {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0452,
        #[cfg(feature = "float-ext")]
        Lnp1 {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0453,
        #[cfg(feature = "float-ext")]
        Expm1 {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0454,
        #[cfg(feature = "float-ext")]
        Sqrt {rc @ 1..4: Invert<RoundingMode,3>, supress_flags @ 0: bool} = 0o0455,

        #[cfg(feature = "float")]
        FRaiseExcept {} = 0o0460,
        #[cfg(feature = "float")]
        FTriggerExcept {} = 0o0461,

        Xchg {} = 0o1000,
        Cmpxchg {} = 0o1001,
        Wcmpxchg {} = 0o1002,
        Fence {} = 0o1003,

        #[cfg(feature = "rand")]
        Rpoll { reg @ 0..4: CleverRegister} = 0o1060,

        #[cfg(feature = "hash-accel")]
        Sipround {} = 0o1070,

        #[cfg(feature = "hash-accel")]
        FusedMul {op @ 0..3: AluOp} = 0o1072,
        #[cfg(feature = "hash-accel")]
        FusedImul {op @ 0..3: AluOp} = 0o1073,
        #[cfg(feature = "hash-accel")]
        CrcAccum {top @ 0: bool} = 0o1074,
        #[cfg(feature = "hash-accel")]
        Crc32Accum {top @ 0: FixedField<bool,1>} = 0o1075,


        #[cfg(feature = "vector")]
        Vec {elem_size @ 0..2: SizeControl} = 0o2000,
        #[cfg(feature = "vector")]
        Vmov {} = 0o2001,
        #[cfg(feature = "vector")]
        Vshuffle {elem_size @ 0..2: SizeControl} = 0o2002,
        #[cfg(feature = "vector")]
        Vextract {dst @ 0..4: CleverRegister} = 0o2003,
        #[cfg(feature = "vector")]
        Vcmp {elem_size @ 0..2: SizeControl} = 0o2004,
        #[cfg(feature = "vector")]
        Vtest {elem_size @ 0..2: SizeControl} = 0o2005,
        #[cfg(all(feature = "vector", feature = "float"))]
        Vfcmp {elem_size @ 0..2: SizeControl} = 0o2006,


        Halt {} = 0o4001,
        Pcfl {} = 0o4002,
        FlAll {} = 0o4003,
        Iflush {} = 0o4004,
        Dflush {} = 0o4005,
        In {size @ 0..2: SizeControl} = 0o4006,
        Out {size @ 0..4: SizeControl} = 0o4007,

        StoRegf {} = 0o4010,
        RstoRegf {} = 0o4011,
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    pub enum ConditionCode{
        Parity = 0,
        Carry = 1,
        Overflow = 2,
        Zero = 3,
        LessThan = 4,
        LessEqual = 5,
        BelowEqual = 6,
        Minus = 7,
        Plus = 8,
        Above = 9,
        GreaterThan = 10,
        GreaterEqual = 11,
        NonZero = 12,
        NoOverflow = 13,
        NoCarry = 14,
        NoParity = 16,
    }
}

bitfield! {
    pub struct CondBranch : BeU16{
        pub ss @ 10..12: ShiftSizeControl,
        pub rel @ 8: bool,
        pub cc @ 4..8: ConditionCode,
        pub weight @ 0..4: SignExt<LeI8, 4>,
    }
}

bitfield! {
    pub struct UncondBranch : BeU16{
        pub rel @ 8: bool,
        pub opcode @ 0..8: UncondBranchOpcode,
    }
}

def_enum! {
    #[repr(BeU8)]
    pub enum UncondBranchOpcode @ 4..8{
        #![non_exhaustive]
        Jmp{ss @ 0..2: ShiftSizeControl} = 0,
        Call{ss @ 0..2: ShiftSizeControl} = 1,
        Fcall{ss @ 0..2: ShiftSizeControl} = 2,
        Ret{} = 3,
        Scall{} = 4,
        Int{int @ 0..4: LeU8} = 5,
        Ijmp{reg @ 0..4: CleverRegister} = 6,
        Icall{reg @ 0..4: CleverRegister} = 7,
        Ifcall{} = 8,
        JmpSM{} = 9,
        CallSM{save @ 0: bool} = 10,
        RetRsm{} = 11,
    }
}

def_enum! {
    #[repr(BeU8)]
    pub enum SuperBranchOpcode @ 4..8 {
        #![non_exhaustive]
        Scret{} = 6,
        RetI{} = 7
    }
}

bitfield! {
    pub struct SuperUncondBranch : BeU16{
        pub rel @ 8: bool,
        pub opcode @ 0..8: SuperBranchOpcode,
    }
}

macro_rules! capturing_enum{
    {
        #[repr($base_ty:ident)]
        $(#[$outer_meta:meta])*
        $vis:vis enum $gname:ident @ $(#[$opcode_meta:meta])* $opcstart:literal .. $opcend:literal {
            $(#![$enum_meta:meta])*
            $($uop:ident ($field:ty) = $uopc:literal,)*
            #[default] $last_uop:ident ($last_field:ty)
            $(,)?
        }
    } => {

        paste!{
            $(#[$outer_meta])*
            $(#[$enum_meta])*
            #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
            $vis enum $gname{
                $($uop($field),)*
                $last_uop($last_field),
            }
            bitfield!{
                $(#[$outer_meta])*
                $vis struct [<$gname Encoded>]: $base_ty{
                    $vis decodebits @ 0..$opcstart : $base_ty,
                    $(#[$opcode_meta])*
                    $vis discrim @ $opcstart .. $opcend : $base_ty,
                }
            }

            $(#[$outer_meta])*
            impl [<$gname Encoded>]{
                $vis fn decode(self) -> $gname{
                    match self.discrim().get(){
                        $($uopc => $gname :: $uop(<$field>::from_bits(self.decodebits())),)*
                        _ => $gname:: $last_uop(<$last_field>::from_bits(self.bits()))
                    }
                }
            }

            $(#[$outer_meta])*
            impl $gname{
                $vis fn encode(self) -> [<$gname Encoded>]{
                    match self{
                        $(Self:: $uop(field) => [<$gname Encoded>]::with_discrim(<$base_ty>::new($uopc)).insert_decodebits(field.to_bits()),)*
                        Self:: $last_uop (last_field) => [<$gname Encoded>]::from_bits(last_field.to_bits())
                    }
                }
            }

            $(#[$outer_meta])*
            impl<R: ::clever_emu_primitives::bitfield::BitfieldTy> ::clever_emu_primitives::bitfield::FromBitfield<R> for $gname where [<$gname Encoded>]: ::clever_emu_primitives::bitfield::FromBitfield<R>,
                $($field: ::clever_emu_primitives::bitfield::FromBitfield::<R>,)* $last_field: ::clever_emu_primitives::bitfield::FromBitfield::<R>{
                fn validate(self) -> bool{
                    match self{
                        $( Self:: $uop(payload) => ::clever_emu_primitives::bitfield::FromBitfield::<R>::validate(payload),)*
                        Self::$last_uop(payload) => ::clever_emu_primitives::bitfield::FromBitfield::<R>::validate(payload)
                    }
                }

                fn from_bits(bits: R) -> Self{
                    <[<$gname Encoded>] as ::clever_emu_primitives::bitfield::FromBitfield::<R>>::from_bits(bits).decode()
                }

                fn to_bits(self) -> R{
                    <[<$gname Encoded>] as ::clever_emu_primitives::bitfield::FromBitfield::<R>>::to_bits(self.encode())
                }
            }


            $(#[$outer_meta])*
            impl ::clever_emu_primitives::bitfield::DisplayBitfield for $gname{
                fn present(&self) -> bool{
                    true
                }

                fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result{
                    f.write_str(name)?;
                    f.write_str(": ")?;
                    ::core::fmt::Display::fmt(self, f)
                }
            }

            $(#[$outer_meta])*
            impl ::core::fmt::Display for $gname{
                fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                    match self{
                        $(Self:: $uop (payload) => payload.fmt(f),)*
                        Self::$last_uop(payload) => payload.fmt(f)
                    }
                }
            }
        }
    }
}

capturing_enum! {
    #[repr(BeU16)]
    pub enum UserBranch @ 10..12{
        Uncond(UncondBranch) = 3,
        #[default] Cond(CondBranch),
    }
}

capturing_enum! {
    #[repr(BeU16)]
    pub enum SuperBranch @ 9..12{
        Uncond(SuperUncondBranch) = 0x6,
        MachSpecificInstrs(MachInstr) = 0x7,
        #[default] Cond(InvalidEncoding)
    }
}

def_enum! {
    #[repr(BeU16)]
    pub enum MachInstr @ 4..9{
        #![non_exhaustive]

        UndFFF{} = 0x1F
    }
}

capturing_enum! {
    #[repr(BeU16)]
    pub enum InstructionOpcode @ 12..16{
        UserBranch(UserBranch) = 0x7,
        SuperBranch(SuperBranch) = 0xF,
        #[default] NonBranch(NonBranchOpcode)
    }
}

impl InstructionOpcode {
    pub fn is_super(&self) -> bool {
        (self.encode().bits() >> 15) != 0
    }
}
