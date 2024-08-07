use bytemuck::{Pod, Zeroable};
use clever_emu_primitives::{bitfield::*, le_fake_enum, primitive::*};
use clever_emu_regs::*;
use clever_emu_types::{CleverRegister, CpuExecutionMode, SizeControl};
use paste::paste;

macro_rules! microcode_group{
    {
        #[repr($base_ty:ident)]
        $vis:vis enum $gname:ident @ $opcstart:literal .. $opcend:literal {
            $($uop:ident {$($decode_bits:tt)*} = $uopc:literal),* $(,)?
        }
    } => {
        paste!{
            $vis mod [<$gname:snake _bits>]{
                use super::*;
                $(::clever_emu_primitives::bitfield::bitfield!{
                    pub struct $uop : $base_ty{
                        $($decode_bits)*
                    }
                })*
            }

            bitfield!{
                $vis struct [<$gname Uop>]: $base_ty{
                    $vis decodebits @ 0..$opcstart : $base_ty,
                    $vis uopc @ $opcstart .. $opcend : LeU8,
                }
            }

            #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
            $vis enum $gname{
                $($uop ([<$gname:snake _bits>]::$uop),)*
            }

            impl [<$gname Uop>]{
                $vis fn decode(self) -> $gname{
                    match self.uopc().get(){
                        $($uopc => $gname :: $uop ( [<$gname:snake _bits>]::$uop::from_bits(self.decodebits())),)*
                        _ => panic!("Bad decode ROM")
                    }
                }
            }
        }
    }
}

microcode_group! {
    #[repr(BeU16)]
    pub enum Decode @ 12..16{
        Ignore {} = 0,
        Operands { pub opc @ 9..12 : BeU16} = 1,
        HValidMask { pub hvalid @ 8..12 : BeU16 } = 2,
        Prefix { pub prefixop @ 0..12 : BeU16} = 0xF,
    }
}

le_fake_enum! {
    #[repr(BeU16)]
    pub enum AccessType{
        Read = 0,
        Write = 1,
        ReadAddress = 2,
        ReadWrite = 3
    }
}

le_fake_enum! {
    #[repr(BeU16)]
    pub enum UnitType{
        Alu = 0,
        Fpu = 1,
        Io = 2,
        HaccelAsic = 3,
    }
}

bitfield! {
    pub struct SerBits : BeU16{
        pub mem @ 0: bool,
        pub instr @ 1: bool,
        pub addr @ 2: bool,
        pub reg @ 3: bool,
    }
}

microcode_group! {
    #[repr(BeU16)]
    pub enum Dep @ 12..16 {
        End {} = 0,
        AccessOperand {pub access @ 6..8 : AccessType, pub opr @ 10..12: BeU16} = 1,
        AccessReg {pub access @ 1..3 : AccessType, pub reg @ 4..12: BeU16} = 2,
        AccessRegH {pub access @ 1..3 : AccessType } = 3,
        AccessMem { pub access @ 1..3 : AccessType } = 4,
        ExecUnit { pub caps @ 3..6 : BeU16, pub unit_ty @ 8..12: UnitType } = 8,
        Axpi { pub lowbit @ 0 : LeU16} = 9,
        Ser {pub ser @ 0..4 : SerBits, pub bitrest @ 4..12: LeU16} = 0xF,
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    pub enum ProcessorState{
        Halted = 0,
        Paused = 1,
        Reset = 0xE,
        Running = 0xF,
    }
}

microcode_group! {
    #[repr(BeU32)]
    pub enum Exec @ 24..32 {
        End {} = 0,
        Ld {pub unit @ 4..6: LeU8, pub input @ 13..16: LeU8, pub operand @ 21..23: LeU8} = 1,
        RdReg { pub unit @ 4..6: LeU8, pub input @ 13..16: LeU8, pub reg @ 16..24: CleverRegister} = 2,
        RdRegh { pub unit @ 4..6: LeU8, pub input @ 13..16: LeU8} = 3,
        RdImm { pub unit @ 4..6: LeU8, pub val_low @ 6..13: LeU16, pub input @ 13..16 : LeU8, pub val_hi @ 16..24: LeU8} = 4,
        RdIndr { pub size @ 0..3 : SizeControl, pub unit @ 4..6 : LeU8, pub input @ 13..16 : LeU8, pub reg @ 16..24: CleverRegister} = 5,
        St {pub unit @ 4..6: LeU8, pub input @ 13..16: LeU8, pub operand @ 21..23: LeU8} = 17,
        WrReg { pub unit @ 4..6: LeU8, pub input @ 13..16: LeU8, pub reg @ 16..24: CleverRegister} = 18,
        WrRegh { pub unit @ 4..6: LeU8, pub input @ 13..16: LeU8} = 19,
        WrImm { pub unit @ 4..6: LeU8, pub val_low @ 6..13: LeU16, pub input @ 13..16 : LeU8, pub val_hi @ 16..24: LeU8} = 20,
        WrIndr { pub size @ 0..3 : SizeControl, pub unit @ 4..6 : LeU8, pub input @ 13..16 : LeU8, pub reg @ 16..24: CleverRegister} = 21,
        Staf { pub unit @ 4..6: LeU8, pub pos @ 13..15 : LeU8} = 32,
        Stafr { pub unit @ 4..6: LeU8, pub pos @ 13..15 : LeU8, pub reg @ 16..24: CleverRegister} = 33,
        Stafo { pub unit @ 4..6: LeU8, pub pos @ 13..15 : LeU8, pub operand @ 21..23: LeU8} = 34,
        Scf {pub mask @ 8..14 : Flags, pub flags @ 16..22: Flags} = 35,
        Xxu { pub unit @ 4..6 : LeU8, pub function @ 13..16: LeU8} = 48,
        Xxu2{ pub unit1 @ 4..6: LeU8, pub unit2 @ 10..12: LeU8, pub function1 @ 13..16: LeU8, pub function2 @ 21..24 : LeU8} = 49,
        Txiov { pub unit1 @ 4..6: LeU8, pub unit2 @ 10..12: LeU8, pub output1 @ 13..16: LeU8, pub input2 @ 21..24: LeU8} = 50,
        Mxa {pub opr @ 22..24: LeU8} = 64,
        MxaIndr {pub size @ 0..3: SizeControl, pub reg @ 16..24: CleverRegister} = 65,
        Lxa {pub opr @ 22..24: LeU8} = 66,
        LxaIndr {pub size @ 0..3: SizeControl, pub reg @ 16..24: CleverRegister} = 67,
        Uxa {pub opr @ 22..24: LeU8} = 68,
        UxaIndr {pub size @ 0..3: SizeControl, pub reg @ 16..24: CleverRegister} = 69,
        Rxc {pub except @ 20..24: LeU8} = 0x70,
        Empstat{pub state @ 20..24: ProcessorState} = 0x71,
        Chxm{pub reqmode @ 0: CpuExecutionMode} = 0x80,
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
#[repr(C)]
pub struct InsnDecodeInfo {
    pub decode_ops: [DecodeUop; 8],
    pub deps_addr: BeU32,
    pub exec_addr: BeU32,
    pub reserved: [BeU32; 2],
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct UCodeRom<'a>(&'a [BeU32]);

impl<'a> UCodeRom<'a> {
    pub fn open_rom(rom: &'a [BeU32]) -> Self {
        Self(rom)
    }

    pub fn decode_instruction(&self, opc: BeU16) -> &'a InsnDecodeInfo {
        let opc = opc.get() as usize;

        if opc > 0xFFF {
            panic!("invalid opcode {}", opc)
        }

        let offset = opc << 4;

        let slice = &self.0[offset..][..8];

        bytemuck::from_bytes(bytemuck::cast_slice(slice))
    }

    pub fn deps(&self, base_addr: BeU32) -> DepsIter<'a> {
        let addr = base_addr.get() as usize;

        let off = addr << 2;

        let slice = &self.0[off..];

        DepsIter(bytemuck::cast_slice(slice).iter())
    }

    pub fn exec(&self, base_addr: BeU32) -> ExecIter<'a> {
        let addr = base_addr.get() as usize;

        let off = addr << 2;

        let slice = &self.0[off..];

        ExecIter(bytemuck::cast_slice(slice).iter())
    }
}

pub struct DepsIter<'a>(core::slice::Iter<'a, DepUop>);

impl<'a> Iterator for DepsIter<'a> {
    type Item = Dep;

    fn next(&mut self) -> Option<Dep> {
        let val = *self.0.next().expect("Unexpected end of microcode ROM");

        let op = val.decode();

        match op {
            Dep::End(_) => None,
            dep => Some(dep),
        }
    }
}

pub struct ExecIter<'a>(core::slice::Iter<'a, ExecUop>);

impl<'a> Iterator for ExecIter<'a> {
    type Item = Exec;

    fn next(&mut self) -> Option<Exec> {
        let val = *self.0.next().expect("Unexpected end of microcode ROM");

        let op = val.decode();

        match op {
            Exec::End(_) => None,
            exec => Some(exec),
        }
    }
}
