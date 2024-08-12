use clever_emu_primitives::primitive::*;

use clever_emu_errors::*;
use clever_emu_types::*;

use crate::decode::{FromInstructionStream, InstructionStream, WideInt};

use crate::op::*;

def_enum! {
    #[repr(BeU16)]
    pub enum OperandCs @ 14..16 {
        Register { reg @ 0..8: CleverRegister,  ss @ 8..11: SizeControl, #[cfg(feature = "vector")]  vec @ 13: bool} = 0,
        Indirect { base @ 0..4: CleverRegister,  ss @ 4..7: SizeControl,  scale @ 7..10: LeU8,  index @ 10..14: CleverRegister} = 1,
        SmallImm { rel @ 12: bool,  imm @ 0..12: LeU16} = 2,
        LargeImm { index @ 0..4: CleverRegister,  zz @ 4..7: SizeControl,  ss @ 8..10: ShiftSizeControl,  rel @ 10: bool,  disp @ 11: bool,  mem @ 13: bool} context ss: ShiftSizeControl = 3,
    }
}

use operand_cs_bits::*;

macro_rules! mk_recursive_pattern{
    ($id:ident @ $last:ident) => {
        $last ($id)
    };
    ($id:ident @ $first:ident $(:: $rest:ident)+) => {
        $first (mk_recursive_pattern!($id @ $($rest)::+))
    };
}

macro_rules! encoded_enum {
    {
        $(use $($ident:ident)::+ $(::* $(@ $_val1:tt)?)?;)*

        $(#[$all_meta:meta])*
        $(pub $(($($tt:tt)*))?)? enum $name:ident : $base_ty:ty {
            $(#![$enum_meta:meta])*
            $($(#[$var_meta:meta])* $(($($prefix_variants:ident)::*))? $variant:ident ($($field_ty:ty),* $(,)?)),*
            $(,)?
        }
    } => {
        $(#[$all_meta])*
        $(#[$enum_meta])*
        $(pub $(($($tt)*))?)? enum $name {
            $($(#[$var_meta])* $variant ($variant, $($field_ty),*)),*
        }

        $(#[$all_meta])*
        impl FromInstructionStream<$base_ty> for $name{
            fn decode<I: InstructionStream>(it: &mut I, base: $base_ty) -> CPUResult<Self>{
                $(use $($ident)::+ $(::* $(@ $_val1)?)?;)*

                match base {
                    $(
                        $(#[$var_meta])* mk_recursive_pattern!(variant @ $($($prefix_variants ::)*)? $variant) => {
                            paste::paste!{
                                $(let [<_ ${index()}>] = <$field_ty as $crate::decode::FromInstructionStream<_>>::decode(it, $crate::decode::AsDecodeContext::as_context(&variant))?;)*

                                Ok(Self::$variant(variant $(, ${ignore($field_ty)} [<_ ${index()}>])*))
                            }

                        }
                    )*
                    _ => Err(CPUException::Undefined)
                }
            }
        }
    }
}

encoded_enum! {
    use OperandCs::*;
    pub enum Operand : OperandCs{
        Register(),
        Indirect(),
        SmallImm(),
        LargeImm(WideInt)
    }
}

impl FromInstructionStream<()> for Operand {
    fn decode<I: InstructionStream>(stream: &mut I, _: ()) -> CPUResult<Self> {
        let cs = OperandCs::decode(stream, ())?;

        <Self as FromInstructionStream<OperandCs>>::decode(stream, cs)
    }
}

use crate::op::mach_instr_bits::*;
use crate::op::non_branch_opcode_bits::*;
use crate::op::uncond_branch_opcode_bits::*;

encoded_enum! {
    use crate::op::UncondBranchOpcode::*;
    pub enum UncondBranchInstruction : UncondBranchOpcode {
        Jmp(WideInt),
        Call(WideInt),
        Fcall(WideInt),
        Ret(),
        Scall(),
        Int(),
        Ijmp(),
        Icall(),
        Ifcall(),
        JmpSM(WideInt),
        CallSM(WideInt),
        RetRsm(),
    }
}

encoded_enum! {
    use crate::op::NonBranchOpcode::*;
    use crate::op::InstructionOpcode::*;
    use crate::op::UserBranch::*;
    use crate::op::SuperBranch::*;
    use crate::op::MachInstr::*;

    pub enum Instruction : InstructionOpcode{
        #![non_exhaustive]
        (NonBranch) Und (),
        (NonBranch) Add(Operand, Operand),
        (NonBranch) Sub(Operand, Operand),
        (NonBranch) And(Operand, Operand),
        (NonBranch) Or(Operand, Operand),
        (NonBranch) Xor(Operand, Operand),
        (NonBranch) Mul(),
        (NonBranch) Div(),
        (NonBranch) Mov(Operand, Operand),
        (NonBranch) Lea(Operand, Operand),
        (NonBranch) MovGpDst(Operand),
        (NonBranch) MovGpSrc(Operand),
        (NonBranch) LeaGpDst(Operand),
        (NonBranch) Nop0(),
        (NonBranch) Nop1(Operand),
        (NonBranch) Nop2(Operand, Operand),
        (NonBranch) Nop3(Operand, Operand, Operand),
        (NonBranch) Push(Operand),
        (NonBranch) Pop(Operand),
        (NonBranch) PushGp(),
        (NonBranch) PopGp(),
        (NonBranch) StoGpr(Operand),
        (NonBranch) StoAr(Operand),
        (NonBranch) RstoGpr(Operand),
        (NonBranch) RstoAr(Operand),
        (NonBranch) PushGpr(),
        (NonBranch) PushAr(),
        (NonBranch) PopGpr(),
        (NonBranch) PopAr(),
        (NonBranch) MovSx(Operand, Operand),
        (NonBranch) Bswap(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) MovIf(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) MovXf(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) MovFi(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) MovFx(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) CvtF(Operand, Operand),
        (NonBranch) Lsh(Operand, Operand),
        (NonBranch) Rsh(Operand, Operand),
        (NonBranch) Arsh(Operand, Operand),
        (NonBranch) LshC(Operand, Operand),
        (NonBranch) RshC(Operand, Operand),
        (NonBranch) Lrot(Operand, Operand),
        (NonBranch) Rrot(Operand, Operand),
        (NonBranch) LshGpDest(Operand),
        (NonBranch) RshGpDest(Operand),
        (NonBranch) ArshGpDest(Operand),
        (NonBranch) LshCGpDest(Operand),
        (NonBranch) RshCGpDest(Operand),
        (NonBranch) LrotGpDest(Operand),
        (NonBranch) RrotGpDest(Operand),
        (NonBranch) Imul(),
        (NonBranch) AddGpDest(Operand),
        (NonBranch) SubGpDest(Operand),
        (NonBranch) AndGpDest(Operand),
        (NonBranch) OrGpDest(Operand),
        (NonBranch) XorGpDest(Operand),
        (NonBranch) Bnot(Operand),
        (NonBranch) Neg(Operand),
        (NonBranch) Idiv(),
        (NonBranch) AddGpSrc(Operand),
        (NonBranch) SubGpSrc(Operand),
        (NonBranch) AndGpSrc(Operand),
        (NonBranch) OrGpSrc(Operand),
        (NonBranch) XorGpSrc(Operand),
        (NonBranch) BnotGp(),
        (NonBranch) NegGp(),
        (NonBranch) CmovT(Operand, Operand, Operand),
        (NonBranch) Cmov(Operand, Operand),
        (NonBranch) Cmp(Operand, Operand),
        (NonBranch) Test(Operand, Operand),
        #[cfg(feature = "hash-accel")]
        (NonBranch) Pload(Operand, Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) Round(Operand),
        #[cfg(feature = "float")]
        (NonBranch) Fabs(Operand),
        #[cfg(feature = "float")]
        (NonBranch) Fneg(Operand),
        #[cfg(feature = "float")]
        (NonBranch) Finv(Operand),
        #[cfg(feature = "float")]
        (NonBranch) Fadd(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) Fsub(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) Fmul(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) Fdiv(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) Frem(Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) Ffma(Operand, Operand, Operand),
        #[cfg(feature = "float")]
        (NonBranch) Fcmpz(Operand),
        #[cfg(feature = "float")]
        (NonBranch) Fcmp(Operand, Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Exp(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Ln(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Lg(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Sin(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Cos(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Tan(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Asin(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Acos(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Atan(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Exp2(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Log10(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Lnp1(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Expm1(Operand),
        #[cfg(feature = "float-ext")]
        (NonBranch) Sqrt(Operand),
        #[cfg(feature = "float")]
        (NonBranch) FRaiseExcept(),
        #[cfg(feature = "float")]
        (NonBranch) FTriggerExcept(),
        (NonBranch) Xchg(Operand, Operand),
        (NonBranch) Cmpxchg(Operand, Operand, Operand),
        (NonBranch) Wcmpxchg(Operand, Operand, Operand),
        (NonBranch) Fence(),
        #[cfg(feature = "rand")]
        (NonBranch) Rpoll(),
        #[cfg(feature = "hash-accel")]
        (NonBranch) Sipround(Operand, Operand),
        #[cfg(feature = "hash-accel")]
        (NonBranch) FusedMul(Operand, Operand, Operand),
        #[cfg(feature = "hash-accel")]
        (NonBranch) FusedImul(Operand, Operand, Operand),
        #[cfg(feature = "hash-accel")]
        (NonBranch) CrcAccum(Operand, Operand, Operand),
        #[cfg(feature = "hash-accel")]
        (NonBranch) Crc32Accum(Operand, Operand, Operand),
        #[cfg(feature = "vector")]
        (NonBranch) Vec(Box<Instruction>),
        #[cfg(feature = "vector")]
        (NonBranch) Vmov(Operand, Operand),
        #[cfg(feature = "vector")]
        (NonBranch) Vshuffle(Operand, Operand),
        #[cfg(feature = "vector")]
        (NonBranch) Vextract(Operand, Operand),
        #[cfg(feature = "vector")]
        (NonBranch) Vcmp(Operand, Operand, Operand),
        #[cfg(feature = "vector")]
        (NonBranch) Vtest(Operand, Operand, Operand),
        #[cfg(all(feature = "vector", feature = "float"))]
        (NonBranch) Vfcmp(Operand, Operand, Operand),

        (UserBranch) CondBranch(WideInt),
        (UserBranch) UncondBranch(UncondBranchInstruction),
        (NonBranch) Halt(),
        (NonBranch) Dflush(Operand),
        (NonBranch) Iflush(Operand),
        (NonBranch) In(),
        (NonBranch) Out(),
        (NonBranch) StoRegf(Operand),
        (NonBranch) RstoRegf(Operand),
        (SuperBranch) SuperUncondBranch(),
        (SuperBranch :: MachSpecificInstrs) UndFFF(),
    }
}

impl<Ctx> FromInstructionStream<Ctx> for Box<Instruction>
where
    Instruction: FromInstructionStream<Ctx>,
{
    fn decode<I: InstructionStream>(stream: &mut I, ctx: Ctx) -> CPUResult<Self> {
        Instruction::decode(stream, ctx).map(Box::new)
    }
}

impl FromInstructionStream<()> for Instruction {
    fn decode<I: InstructionStream>(stream: &mut I, _: ()) -> CPUResult<Self> {
        let cs = InstructionOpcode::decode(stream, ())?;

        <Self as FromInstructionStream<InstructionOpcode>>::decode(stream, cs)
    }
}
