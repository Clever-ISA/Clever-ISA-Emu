use clever_emu_errors::CPUResult;
use clever_emu_primitives::{
    bitfield::FromBitfield,
    primitive::{BeU128, BeU16, LeU128},
};
use clever_emu_types::{ShiftSizeControl, SizeControl};

pub trait InstructionStream {
    fn next_iword(&mut self) -> CPUResult<BeU16>;

    fn fetch<T: FromInstructionStream<()>>(&mut self) -> CPUResult<T>
    where
        Self: Sized,
    {
        T::decode(self, ())
    }
}

impl<'a, I: InstructionStream + ?Sized> InstructionStream for &'a mut I {
    fn next_iword(&mut self) -> CPUResult<BeU16> {
        I::next_iword(self)
    }
}

pub trait FromInstructionStream<Ctx>: Sized {
    fn decode<I: InstructionStream>(stream: &mut I, ctx: Ctx) -> CPUResult<Self>;
}

impl<B, Ctx> FromInstructionStream<Ctx> for B
where
    B: FromBitfield<BeU16> + Copy,
{
    fn decode<I: InstructionStream>(stream: &mut I, _: Ctx) -> CPUResult<Self> {
        let val = B::from_bits(stream.next_iword()?);

        if val.validate() {
            Ok(val)
        } else {
            Err(clever_emu_errors::CPUException::Undefined)
        }
    }
}

/// Marker trait to default implement [`AsDecodeContext`] for type `()`
pub trait NoContext {}

pub trait AsDecodeContext {
    type Context: Sized;

    fn as_context(&self) -> Self::Context;
}

impl<C: NoContext> AsDecodeContext for C {
    type Context = ();

    fn as_context(&self) {}
}

#[repr(transparent)]
pub struct WideInt(pub LeU128);

impl FromInstructionStream<ShiftSizeControl> for WideInt {
    fn decode<I: InstructionStream>(stream: &mut I, ctx: ShiftSizeControl) -> CPUResult<Self> {
        let mut le_int = LeU128::new(0);

        for i in 0..(ctx.as_bytes() as u32 >> 1) {
            le_int |= stream.next_iword()?.to_le().unsigned_as::<LeU128>() << (16 * i);
        }

        Ok(Self(le_int))
    }
}
