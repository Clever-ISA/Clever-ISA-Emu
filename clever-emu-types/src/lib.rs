use clever_emu_primitives::{bitfield, le_fake_enum, primitive::*};

use bytemuck::{Pod, Zeroable};

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Extension {
    Main = 0,
    Float = 1,
    FloatExt = 2,
    Vector = 3,
    XmRand = 4,
    Virt = 5,
    Haccell = 6,
}

le_fake_enum! {
    #[repr(LeU8)]
    pub enum SizeControl{
        Byte = 0,
        Half = 1,
        Word = 2,
        Double = 3,
        Quad = 4,
    }
}

impl SizeControl {
    #[inline]
    pub fn as_bits(self) -> LeU64 {
        LeU64::new(8) << self.0.unsigned_as::<LeU64>()
    }

    #[inline]
    pub fn as_bytes(self) -> LeU64 {
        LeU64::new(1) << self.0.unsigned_as::<LeU64>()
    }

    #[inline]
    pub fn as_regwidth_mask(self) -> LeU64 {
        LeU64::new(2) << (self.as_bits() - 1)
    }

    #[inline]
    pub fn as_vectorwidth_mask(self) -> LeU128 {
        LeU128::new(2) << (self.as_bits() - 1).unsigned_as::<LeU128>()
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    pub enum ShiftSizeControl{
        Half = 0,
        Word = 1,
        Double = 2,
        Quad = 3,
    }
}

impl ShiftSizeControl {
    #[inline]
    pub fn as_size_control(self) -> SizeControl {
        SizeControl(self.0 + 1)
    }

    #[inline]
    pub fn as_bits(self) -> LeU64 {
        LeU64::new(16) << self.0.unsigned_as::<LeU64>()
    }

    #[inline]
    pub fn as_bytes(self) -> LeU64 {
        LeU64::new(2) << self.0.unsigned_as::<LeU64>()
    }

    #[inline]
    pub fn as_regwidth_mask(self) -> LeU64 {
        LeU64::new(2) << (self.as_bits() - 1)
    }

    #[inline]
    pub fn as_vectorwidth_mask(self) -> LeU128 {
        LeU128::new(2) << (self.as_bits() - 1).unsigned_as::<LeU128>()
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, Hash, PartialEq, Eq, Pod, Zeroable)]
pub struct CleverRegister(pub u8);

impl CleverRegister {
    pub const fn get(self) -> u8 {
        self.0
    }
}

macro_rules! clever_registers{
    {
        $($name:ident $(| $altnames:ident)* => $val:expr),* $(,)?
    } => {
        #[allow(non_upper_case_globals)]
        impl CleverRegister{
            $(pub const $name: Self = Self($val); $(pub const $altnames: Self = Self($val);)*)*


            pub const fn validate(self) -> bool{
                match self{
                    $(Self::$name => true,)*
                    _ => false,
                }
            }
        }

        impl ::core::fmt::Display for CleverRegister{
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result{
                match self.0{
                    $($val => f.write_str(::core::stringify!($name)),)*
                    val => f.write_fmt(::core::format_args!("r{}",val))
                }
            }
        }

        impl ::core::fmt::Debug for CleverRegister{
            fn fmt(&self, f: &mut core::fmt::Formatter) -> ::core::fmt::Result{
                struct DontEscape(&'static str);
                impl ::core::fmt::Debug for DontEscape{
                    fn fmt(&self, f: &mut core::fmt::Formatter) -> ::core::fmt::Result{
                        f.write_str(self.0)
                    }
                }

                match self.0{
                    $($val => {
                        f.debug_tuple("CleverRegister")
                            .field(&DontEscape(::core::stringify!($name))).finish()
                    })*
                    val => f.debug_tuple("CleverRegister").field(&val).finish()
                }
            }
        }
    }
}

clever_registers! {
    r0 | racc => 0,
    r1 | rsrc => 1,
    r2 | rdst => 2,
    r3 | rcnt => 3,
    r4 => 4,
    r5 => 5,
    r6 | fbase => 6,
    r7 | sptr => 7,
    r8 => 8,
    r9 => 9,
    r10 => 10,
    r11 => 11,
    r12 => 12,
    r13 => 13,
    r14 => 14,
    r15 | link => 15,
    ip => 16,
    flags => 17,
    mode => 18,
    fpcw => 19,
    f0 => 24,
    f1 => 25,
    f2 => 26,
    f3 => 27,
    f4 => 28,
    f5 => 29,
    f6 => 30,
    f7 => 31,
    v0l => 64,
    v0h => 65,
    v1l => 66,
    v1h => 67,
    v2l => 68,
    v2h => 69,
    v3l => 70,
    v3h => 71,
    v4l => 72,
    v4h => 73,
    v5l => 74,
    v5h => 75,
    v6l => 76,
    v6h => 77,
    v7l => 78,
    v7h => 79,
    v8l => 80,
    v8h => 81,
    v9l => 82,
    v9h => 83,
    v10l => 84,
    v10h => 85,
    v11l => 86,
    v11h => 87,
    v12l => 88,
    v12h => 89,
    v13l => 90,
    v13h => 91,
    v14l => 92,
    v14h => 93,
    v15l => 94,
    v15h => 95,
    cr0 => 128,
    page | cr1 => 129,
    flprotected | cr2 => 130,
    scdp | cr3 => 131,
    scsp | cr4 => 132,
    sccr | cr5 => 133,
    itabp | cr6 => 134,
    ciread | cr7 => 135,
    cpuidlo => 136,
    cpuidhi => 137,
    cpuex2 => 138,
    cpuex3 => 139,
    cpuex4 => 140,
    cpuex5 => 141,
    cpuex6 => 142,
    mscpuex => 143,
    fcode | cr8 => 144,
    pfchar | cr9 => 145,
    msr0 => 148,
    msr1 => 149,
    msr2 => 150,
    msr3 => 151,
    msr4 => 152,
    msr5 => 153,
    msr6 => 154,
    rdinfo => 156
}

impl<T: bitfield::BitfieldTy> bitfield::FromBitfield<T> for CleverRegister
where
    LeU8: bitfield::FromBitfield<T>,
{
    fn from_bits(bits: T) -> Self {
        Self(LeU8::from_bits(bits).get())
    }

    fn to_bits(self) -> T {
        LeU8::new(self.0).to_bits()
    }

    fn validate(self) -> bool {
        LeU8::new(self.0).validate() && self.validate()
    }
}

impl bitfield::DisplayBitfield for CleverRegister {
    fn present(&self) -> bool {
        true
    }

    fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use core::fmt::Display;
        f.write_str(name)?;
        f.write_str("(")?;
        self.fmt(f)?;
        f.write_str(")")
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct CheckModeError;

le_fake_enum! {
    #[repr(LeU8)]
    #[derive(PartialOrd, Ord)]
    pub enum CpuExecutionMode{
        Supervisor = 0,
        User = 1,
    }
}

impl CpuExecutionMode {
    pub fn check_mode(self, required_rights: CpuExecutionMode) -> Result<(), CheckModeError> {
        if self > required_rights {
            Err(CheckModeError)
        } else {
            Ok(())
        }
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct CheckValidError;

bitfield! {
    pub struct ExecutionMode : LeU8{
        xm @ 0: CpuExecutionMode,
        xmm @ 1: bitfield::Sentinel<CpuExecutionMode>,
    }
}

impl ExecutionMode {
    #[inline]
    pub fn from_mode(mode: CpuExecutionMode) -> Self {
        Self::with_xm(mode) | Self::with_xmm(bitfield::Sentinel(mode))
    }

    #[inline]
    pub fn check_valid_error(&self) -> Result<(), CheckValidError> {
        if !self.validate() {
            Err(CheckValidError)
        } else if self.xm() != self.xmm().0 {
            Err(CheckValidError)
        } else {
            Ok(())
        }
    }

    #[inline]
    pub fn mode(self) -> CpuExecutionMode {
        self.xm()
    }
}
