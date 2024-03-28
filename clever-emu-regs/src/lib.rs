pub mod cpuid;

use bytemuck::{Pod, Zeroable};

use clever_emu_primitives::{bitfield, le_fake_enum, primitive::*};

#[cfg(feature = "float")]
use clever_emu_primitives::float::*;

use clever_emu_types::{
    CleverRegister, CpuExecutionMode, ExecutionMode, Extension, ShiftSizeControl,
};

use clever_emu_errors::{CPUException, CPUResult};

macro_rules! safe_union{
    {
        $(#[$meta:meta])*
        $vis:vis union $union_name:ident{
            $($(#[$meta2:meta])* $vis2:vis $field_name:ident : $ty:ty),*  $(,)?
        }
    } => {
        $(#[$meta])*
        #[repr(C)]
        #[derive(Copy, Clone)]
        $vis union $union_name{
            $($(#[$meta2])* $vis2 $field_name : $ty),*

        }

        unsafe impl ::bytemuck::Zeroable for $union_name{}
        unsafe impl ::bytemuck::Pod for $union_name{}

        impl $union_name{
            $(
                $vis2 const fn $field_name(self) -> $ty{
                    const __TYCHECK: () = {
                        fn __check_impls_pod(this: $union_name) -> impl ::bytemuck::Pod{
                            unsafe{core::mem::transmute::<_,$ty>(this)}
                        }
                    };

                    unsafe{self.$field_name}
                }

            )*
        }
    }
}

safe_union! {
    #[repr(align(16))]
    pub union VectorPair{
        pub u128x1: LeU128,
        pub u64x2:  [LeU64;2],
        pub u32x4:  [LeU32;4],
        pub u16x8:  [LeU16;8],
        pub u8x16:  [LeU8;16],
        #[cfg(feature = "float")]
        pub f128x1: CleverF128,
        #[cfg(feature = "float")]
        pub f64x2:  [CleverF64;2],
        #[cfg(feature = "float")]
        pub f32x4:  [CleverF32;4],
        #[cfg(feature = "float")]
        pub f16x8:  [CleverF16;8],
    }
}

impl ::core::fmt::Debug for VectorPair {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        self.u64x2().fmt(f)
    }
}

bitfield! {
    pub struct Flags : LeU64{
        pub carry @ 0 : bool,
        pub zero @ 1 : bool,
        pub overflow @ 2 : bool,
        pub negative @ 3 : bool,
        pub parity @ 4 : bool,
    }
}

bitfield! {
    pub struct Mode : LeU64{
        pub xm @ 32..34 : ExecutionMode,
    }
}

bitfield! {
    #[cfg(feature = "float")]
    pub struct Fpcw : LeU64{
        pub rnd @ 0..3 : RoundingMode,
        pub flush_denorm @ 4 : bool,
        pub except @ 8..16 : FpException,
        pub emask @ 16..24 : FpException,
        pub emaskall @ 24 : bool,
        pub xopss @ 25..27 : ShiftSizeControl
    }
}

#[cfg(feature = "float")]
impl Fpcw {
    pub fn check_valid(&self) -> CPUResult<()> {
        if !self.validate() {
            Err(CPUException::Undefined)
        } else if !self.except().validate() {
            Err(CPUException::Undefined)
        } else if !self.emask().validate() {
            Err(CPUException::Undefined)
        } else if !self.rnd().validate() {
            Err(CPUException::Undefined)
        } else {
            Ok(())
        }
    }
}

bitfield! {
    pub struct Cr0 : LeU64{
        pub pg @ 0: bool,
        pub ie @ 1 : bool,
        #[cfg(feature = "float")]
        pub fp @ 6 : bool,
        #[cfg(feature = "float")]
        pub fpexcept @ 7: bool,
        #[cfg(feature = "vector")]
        pub vec @ 8: bool,
        #[cfg(feature = "rand")]
        pub xmrand @ 9: bool,
        #[cfg(feature = "rand")]
        pub rpollinfo @ 10: bool,
        #[cfg(feature = "hash-accel")]
        pub haccel @ 11 : bool,
    }
}

impl Cr0 {
    pub fn check_valid(&self) -> CPUResult<()> {
        if !self.validate() {
            Err(CPUException::Undefined)
        } else {
            Ok(())
        }
    }

    pub fn check_extension(&self, ex: Extension) -> CPUResult<()> {
        match ex {
            Extension::Main => Ok(()),
            #[cfg(feature = "float")]
            Extension::Float if self.fp() => Ok(()),
            #[cfg(feature = "float-ext")]
            Extension::FloatExt if self.fp() => Ok(()),
            #[cfg(feature = "vector")]
            Extension::Vector if self.vec() => Ok(()),
            #[cfg(feature = "rand")]
            Extension::XmRand if self.xmrand() => Ok(()),
            #[cfg(feature = "hash-accel")]
            Extension::Haccell if self.haccel() => Ok(()),
            _ => Err(CPUException::Undefined),
        }
    }
}

bitfield! {
    pub struct Sccr : LeU64{
        pub fx @ 1: bool,
    }
}

impl Sccr {
    pub fn check_valid(&self) -> CPUResult<()> {
        if !self.validate() {
            Err(CPUException::Undefined)
        } else {
            Ok(())
        }
    }
}

bitfield! {
    pub struct Ciread : LeU64{
        pub cpuidlo @ 0: bool,
        pub cpuidhi @ 1: bool,
        pub cpuex @ 2..7: LeU8,
        pub mscpuex @ 7: bool,
    }
}

impl Ciread {
    pub fn check_valid(&self) -> CPUResult<()> {
        if !self.validate() {
            Err(clever_emu_errors::CPUException::Undefined)
        } else {
            Ok(())
        }
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    pub enum RandFailCode{
        Unvail = 0,
        Reset = 1,
        Fault = 2,
        Pause = 3,
    }
}

bitfield! {
    pub struct RPollInfo: LeU64{
        pub enthropy @ 0..16: LeU16,
        pub fail @ 16..18: RandFailCode,
        pub repeat @ 18: bool,
    }
}

bitfield! {
    pub struct PgTab : LeU64{
        pub ptl @ 0..3 : LeU8,
        pub addr @ 12..64 : LeU64,
    }
}

impl PgTab {
    pub fn page_addr(self) -> LeU64 {
        self.addr() << 12
    }

    pub fn check_valid(self) -> CPUResult<()> {
        if !self.validate() {
            Err(CPUException::Undefined)
        } else if self.ptl() > 4 {
            Err(CPUException::Undefined)
        } else {
            Ok(())
        }
    }
}

#[repr(C, align(2048))]
#[derive(Copy, Clone, Pod, Zeroable)]
#[non_exhaustive]
pub struct NamedRegs {
    pub gprs: [LeU64; 16],
    pub ip: LeI64,
    pub flags: Flags,
    pub mode: Mode,
    pub fpcw: Fpcw,
    reserved20: [LeU64; 4],
    #[cfg(feature = "float")]
    pub fregs: [CleverFloatReg; 8],
    #[cfg(not(feature = "float"))]
    reserved24: [LeU64; 8],
    reserved32: [LeU64; 32],
    #[cfg(feature = "vector")]
    pub vreg: [VectorPair; 16],
    #[cfg(not(feature = "vector"))]
    reserved64: [LeU64; 32],
    reserved96: [LeU64; 32],
    pub cr0: Cr0,
    pub ptbl: PgTab,
    pub flprotect: Flags,
    pub scdp: LeI64,
    pub scsp: LeI64,
    pub sccr: Sccr,
    pub itabp: LeI64,
    pub ciread: Ciread,
    pub cpuid: [LeU64; 2],
    pub cpuex: [LeU64; 6],
    pub fcode: LeU64,
    pub pfcharptr: LeI64,
    reserved146: [LeU64; 2],
    pub msr: [LeU64; 7],
    reserved155: LeU64,
    #[cfg(feature = "rand")]
    pub rpollinfo: RPollInfo,
    #[cfg(not(feature = "rand"))]
    reserved156: LeU64,
    reserved157: [LeU64; 99],
}

safe_union! {
    pub union Regs{
        pub named: NamedRegs,
        array: [LeU64;256]
    }
}

impl core::ops::Deref for Regs {
    type Target = NamedRegs;

    fn deref(&self) -> &NamedRegs {
        unsafe { &self.named }
    }
}

impl core::ops::DerefMut for Regs {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut self.named }
    }
}

impl Regs {
    pub const fn new(cpuid: [LeU64; 2]) -> Self {
        let mut val = Self {
            array: [LeU64::new(0); 256],
        };

        val.named.ip = LeI64::new(0xFF00);
        val.named.cpuid = cpuid;
        val.named.cpuex = cpuid::CPUEX;
        val
    }

    pub fn validate_before_reading(
        &self,
        regno: CleverRegister,
        mode: CpuExecutionMode,
    ) -> CPUResult<()> {
        match regno {
            CleverRegister(0..=18) => Ok(()),
            CleverRegister(19) | CleverRegister(24..=31) => {
                self.cr0.check_extension(Extension::Float)
            }
            CleverRegister(64..=95) => self.cr0.check_extension(Extension::Vector),
            CleverRegister(128..=135) | CleverRegister::pfchar | CleverRegister::fcode => {
                mode.check_mode(CpuExecutionMode::Supervisor)?;
                Ok(())
            }
            CleverRegister(v @ 136..=143) => {
                let rno = v - 136;

                let ciread = self.ciread;
                if (ciread.bits() & (LeU64::new(1) << (rno as u32))) != LeU64::new(0) {
                    Ok(())
                } else {
                    mode.check_mode(CpuExecutionMode::Supervisor)?;
                    Ok(())
                }
            }
            #[cfg(feature = "rand")]
            CleverRegister(156) => {
                mode.check_mode(CpuExecutionMode::Supervisor)?;
                Ok(())
            }
            _ => Err(CPUException::Undefined),
        }
    }

    pub fn validate_before_writing(
        &self,
        regno: CleverRegister,
        val: LeU64,
        mode: CpuExecutionMode,
    ) -> CPUResult<()> {
        match regno {
            CleverRegister(0..=15) | CleverRegister::flags => Ok(()),
            CleverRegister::ip | CleverRegister::mode => Err(CPUException::Undefined),
            CleverRegister(24..=31) => self.cr0.check_extension(Extension::Float),
            CleverRegister(64..=95) => self.cr0.check_extension(Extension::Vector),
            #[cfg(feature = "float")]
            CleverRegister::fpcw => {
                self.cr0.check_extension(Extension::Float)?;
                let fpcw = Fpcw::from_bits(val);

                fpcw.check_valid()
            }
            CleverRegister::cr0 => {
                mode.check_mode(CpuExecutionMode::Supervisor)?;
                let cr0 = Cr0::from_bits(val);

                cr0.check_valid()
            }
            CleverRegister::page => {
                mode.check_mode(CpuExecutionMode::Supervisor)?;
                let page = PgTab::from_bits(val);

                page.check_valid()
            }
            CleverRegister::scdp
            | CleverRegister::scsp
            | CleverRegister::itabp
            | CleverRegister::pfchar
            | CleverRegister::fcode => {
                mode.check_mode(CpuExecutionMode::Supervisor)?;
                Ok(())
            }
            CleverRegister::sccr => {
                mode.check_mode(CpuExecutionMode::Supervisor)?;
                let sccr = Sccr::from_bits(val);
                sccr.check_valid()
            }
            CleverRegister::ciread => {
                mode.check_mode(CpuExecutionMode::Supervisor)?;
                let ciread = Ciread::from_bits(val);
                ciread.check_valid()
            }
            _ => Err(CPUException::Undefined),
        }
    }
}

impl core::ops::Index<CleverRegister> for Regs {
    type Output = LeU64;
    fn index(&self, index: CleverRegister) -> &Self::Output {
        unsafe { &self.array[index.0 as usize] }
    }
}

impl core::ops::IndexMut<CleverRegister> for Regs {
    fn index_mut(&mut self, index: CleverRegister) -> &mut Self::Output {
        unsafe { &mut self.array[index.0 as usize] }
    }
}
