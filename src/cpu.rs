pub mod reg;
pub mod state;
pub mod ucode;

use std::cell::RefCell;
use std::mem::MaybeUninit;
use std::rc::Rc;

use crate::error::CPUException;
use crate::error::{self, CPUResult};
use crate::mem::{
    Cache, CacheAccessError, CacheAccessResult, CacheAttrs, CacheFetch, CacheInvalidate, CacheLine,
    CacheWrite, LocalMemory, LocalMemoryBus, Status,
};
use crate::primitive::*;

use bytemuck::{Pod, Zeroable};

use crate::util::*;

use crate::bitfield::{bitfield, DisplayBitfield, FromBitfield, Sentinel};

le_fake_enum! {
    #[repr(LeU8)]
    #[derive(PartialOrd, Ord)]
    pub enum CpuExecutionMode{
        Supervisor = 0,
        User = 1,
    }
}

impl CpuExecutionMode {
    pub fn check_mode(self, required_rights: CpuExecutionMode) -> CPUResult<()> {
        if self > required_rights {
            Err(CPUException::SystemProtection(LeU64::new(0)))
        } else {
            Ok(())
        }
    }
}

bitfield! {
    pub struct ExecutionMode : LeU8{
        xm @ 0: CpuExecutionMode,
        xmm @ 1: Sentinel<CpuExecutionMode>,
    }
}

impl ExecutionMode {
    #[inline]
    pub fn from_mode(mode: CpuExecutionMode) -> Self {
        Self::with_xm(mode) | Self::with_xmm(Sentinel(mode))
    }

    #[inline]
    pub fn check_valid(self) -> error::CPUResult<()> {
        if self.xm() != self.xmm().0 {
            Err(error::CPUException::Undefined)
        } else {
            Ok(())
        }
    }

    #[inline]
    pub fn mode(self) -> CpuExecutionMode {
        self.xm()
    }
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
        NotZero = 12,
        NotOverflow = 13,
        NotCarry = 14,
        NotParity = 15,
    }
}

bitfield! {
    pub struct CleverCondBranch : BeU16{
        pub branch_weight @ 0..4: LeU8,
        pub cond @ 4..8: ConditionCode,
        pub rel @ 8: bool,
        pub ss @ 10..12: ShiftSizeControl,
    }
}

le_fake_enum! {
    #[repr(LeU8)]
    pub enum BranchOpcode{
        Jmp = 0,
        Call = 1,
        Fcall = 2,
        Ret = 3,
        Scall = 4,
        Int = 5,
        Ijmp = 8,
        Icall = 9,
        Ifcall = 10,
        Jmpsm = 1,
        Callsm = 12,
        Retrsm = 13,
    }
}

bitfield! {
    pub struct CleverSpecialBranch : BeU16{
        pub branch_opcode @ 0..4: BranchOpcode,
        pub rel @ 4: bool,
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

impl<T: crate::bitfield::BitfieldTy> FromBitfield<T> for CleverRegister
where
    LeU8: FromBitfield<T>,
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

impl DisplayBitfield for CleverRegister {
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

le_fake_enum! {
    #[repr(LeU8)]
    pub enum ProcessorState{
        Halted = 0,
        Paused = 1,
        Reset = 0xE,
        Running = 0xF,
    }
}

pub struct DataCache<M>(LocalMemory<M>);

impl<M> DataCache<M> {
    pub fn new(underlying: M, l1dsize: usize) -> Self {
        Self(LocalMemory::new(underlying, l1dsize))
    }
}

impl<M: CacheFetch> DataCache<M> {
    fn fetch_blocking(&self, line_addr: LeU64) -> CPUResult<CacheLine> {
        let line_addr = line_addr >> 6;
        for i in (0usize..).take(128).chain(core::iter::repeat(128)) {
            match self.0.read_line(line_addr) {
                Ok((line, status)) => return Ok(line),
                Err(CacheAccessError::Exception(ex)) => return Err(ex),
                Err(CacheAccessError::Locked) => {
                    if i < 16 {
                        core::hint::spin_loop()
                    } else if i < 128 {
                        std::thread::yield_now()
                    } else {
                        self.0.park_on_line_unlock(line_addr)
                    }
                }
                Err(e) => unreachable!("Should not be generated {:?}", e),
            }
        }

        unreachable!()
    }
    /// Reads two cache lines in a manner that satisfies the consistency rule
    fn fetch_two_blocking(&self, line_addr: LeU64) -> CPUResult<(CacheLine, CacheLine)> {
        let line_addr = line_addr >> 6;
        let mut lines = [None, None];

        let mut status = Status::Hit;

        for (num, line) in lines.iter_mut().enumerate() {
            let addr = line_addr + (num as u64);
            match self.0.read_line(addr) {
                Ok((val, s)) => {
                    *line = Some(val);
                    status = status & s;
                }
                Err(CacheAccessError::Exception(ex)) => return Err(ex),
                Err(CacheAccessError::Locked) => {}
                Err(e) => unreachable!("Should not be generated {:?}", e),
            }
        }

        if let [Some(l), Some(r)] = lines {
            return Ok((l, r));
        }

        if status == Status::Hit {
            // If a hard read failed because the line was locked, but we hit the other read, we can do a non-probed read, provided it hits
            // If either line we read misses here, though, we have to fallback to a locked read.

            let mut other_line = 0;

            for (num, line) in lines.iter_mut().enumerate() {
                let addr = line_addr + (num as u64);

                if line.is_none() {
                    match self.0.read_line_without_probe(addr) {
                        Ok((val, s)) => {
                            *line = Some(val);
                            status = status & s;
                        }
                        Err(CacheAccessError::Exception(ex)) => return Err(ex),
                        Err(CacheAccessError::Locked) => {}
                        Err(e) => unreachable!("Should not be generated {:?}", e),
                    }
                }
            }
            if status == Status::Hit {
                if let [Some(l), Some(r)] = lines {
                    return Ok((l, r));
                }
            }
        }
        while status != Status::Hit {
            status = Status::Hit;
            for (num, line) in lines.iter_mut().enumerate() {
                let addr = line_addr + (num as u64);
                for i in (0usize..128).chain(core::iter::repeat(128)) {
                    match self.0.read_line(addr) {
                        Ok((val, s)) => {
                            *line = Some(val);

                            if num == 1 {
                                // We can ignore missing the first line, because we'd see the update on it after
                                status = s;
                            }
                            break;
                        }
                        Err(CacheAccessError::Exception(ex)) => return Err(ex),
                        Err(CacheAccessError::Locked) => {
                            if i < 16 {
                                core::hint::spin_loop()
                            } else if i < 128 {
                                std::thread::yield_now()
                            } else {
                                self.0.park_on_line_unlock(addr)
                            }
                        }
                        Err(e) => unreachable!("Should not be generated {:?}", e),
                    }
                }
            }
        }

        if let [Some(l), Some(r)] = lines {
            return Ok((l, r));
        } else {
            unreachable!("We should not have failed to fetch any lines")
        }
    }

    fn fetch_under_lock(&self, line_addr: LeU64) -> CPUResult<CacheLine> {
        match self.0.read_line(line_addr >> 6) {
            Ok((line, _)) => Ok(line),
            Err(CacheAccessError::Exception(ex)) => Err(ex),
            Err(CacheAccessError::Locked) => match self.0.read_line_without_probe(line_addr >> 6) {
                Ok((line, _)) => Ok(line),
                Err(CacheAccessError::Exception(ex)) => Err(ex),
                Err(e) => unreachable!("Should not be generated {:?}", e),
            },
            Err(e) => unreachable!("Should not be generated {:?}", e),
        }
    }

    pub fn read(&self, paddr: LeU64, bytes: &mut [u8]) -> CPUResult<()> {
        let align_to_cache = (paddr + 63) & !63;

        let head_len = (align_to_cache - paddr).get() as usize;

        let first_line = paddr & !63;
        let first_line_offset = (paddr - first_line).get() as usize;

        if head_len < bytes.len() {
            let (head, rest) = bytes.split_at_mut(head_len);

            if rest.len() > 64 {
                panic!("Cannot read more than two cache lines at once")
            }

            let (first, second) = self.fetch_two_blocking(first_line)?;

            let first = &bytemuck::bytes_of(&first)[first_line_offset..];
            let second = &bytemuck::bytes_of(&second)[..rest.len()];
            head.copy_from_slice(first);
            rest.copy_from_slice(second);
        } else {
            let line = self.fetch_blocking(first_line)?;

            let line = &bytemuck::bytes_of(&line)[first_line_offset..][..bytes.len()];

            bytes.copy_from_slice(&line[first_line_offset..]);
        }
        Ok(())
    }
}

pub struct CacheLineLockGuard<'a, M: CacheWrite>(Option<&'a M>, LeU64);

impl<'a, M: CacheWrite> Drop for CacheLineLockGuard<'a, M> {
    fn drop(&mut self) {
        if let Some(mem) = self.0 {
            mem.unlock(self.1)
                .expect("We should own this line, so it must be present");
        }
    }
}

impl<M: CacheWrite> DataCache<M> {
    fn write_back(&self, line_addr: LeU64, val: CacheLine) -> CPUResult<()> {
        let line_addr = line_addr >> 6;

        let res = self.0.write_line(line_addr, val);

        match res {
            Ok(_) => Ok(()),
            Err(CacheAccessError::Exception(ex)) => return Err(ex),
            Err(e) => unreachable!("Should not be generated {:?}", e),
        }
    }

    fn write_back_two(&self, line_addr: LeU64, vals: [CacheLine; 2]) -> CPUResult<()> {
        let line_addr = line_addr >> 6;
        let mut res = [Ok(()), Ok(())];
        for ((num, val), res) in vals.into_iter().enumerate().zip(&mut res) {
            let line_addr = line_addr + (num as u64);
            *res = match self.0.write_line(line_addr, val) {
                Ok(_) => Ok(()),
                Err(CacheAccessError::Exception(ex)) => Err(ex),
                Err(e) => unreachable!("Should not be generated {:?}", e),
            };
        }

        res.into_iter().collect()
    }

    pub fn write(&self, paddr: LeU64, bytes: &[u8]) -> CPUResult<()> {
        let align_to_cache = (paddr + 63) & !63;

        let head_len = (align_to_cache - paddr).get() as usize;

        let first_line = paddr & !63;
        let first_line_offset = (paddr - first_line).get() as usize;
        if head_len < bytes.len() {
            let _guards = (self.lock(first_line)?, self.lock(first_line + 64)?);
            let (head, rest) = bytes.split_at(head_len);

            if rest.len() > 64 {
                panic!("Cannot read more than two cache lines at once")
            }

            let mut first = if head.len() < 64 {
                self.fetch_under_lock(first_line)?
            } else {
                CacheLine::zeroed()
            };

            let mut last = if rest.len() < 64 {
                self.fetch_under_lock(first_line + 64)?
            } else {
                CacheLine::zeroed()
            };

            let first_bytes = &mut bytemuck::bytes_of_mut(&mut first)[first_line_offset..];
            first_bytes.copy_from_slice(head);
            let last_bytes = &mut bytemuck::bytes_of_mut(&mut last)[..rest.len()];
            last_bytes.copy_from_slice(rest);

            self.write_back_two(first_line, [first, last])?;
        } else {
            let _guard = self.lock(first_line)?;
            let mut line = if bytes.len() < 64 {
                self.fetch_under_lock(first_line)?
            } else {
                CacheLine::zeroed()
            };

            let first_bytes = &mut bytemuck::bytes_of_mut(&mut line)[first_line_offset..];
            first_bytes.copy_from_slice(bytes);

            self.write_back(first_line, line)?;
        }

        Ok(())
    }

    pub fn lock(&self, line_addr: LeU64) -> CPUResult<CacheLineLockGuard<LocalMemory<M>>> {
        let line = line_addr >> 6;
        match self.0.probe_attrs(line) {
            Ok((attrs, _)) => {
                if attrs.is_locked() {
                    return Ok(CacheLineLockGuard(None, line));
                }
            }
            Err(CacheAccessError::Exception(ex)) => return Err(ex),
            _ => {}
        }

        for i in (0usize..128).chain(core::iter::repeat(128)) {
            match self.0.lock(line) {
                Ok(_) => return Ok(CacheLineLockGuard(Some(&self.0), line)),
                Err(CacheAccessError::Exception(ex)) => return Err(ex),
                Err(CacheAccessError::Locked) => {
                    if i < 16 {
                        core::hint::spin_loop()
                    } else if i < 128 {
                        std::thread::yield_now()
                    } else {
                        self.0.park_on_line_unlock(line)
                    }
                }
                Err(e) => unreachable!("Should not be generated {:?}", e),
            }
        }
        unreachable!()
    }
}

pub struct InsnCache<M> {
    l1icache: LocalMemory<M>,
    fetch_line: LeU64,
    buffer: [BeU16; 32],
    buffer_pos: usize,
}

impl<M> InsnCache<M> {
    pub fn new(underlying: M, l1isize: usize) -> Self {
        Self {
            l1icache: LocalMemory::new(underlying, l1isize),
            fetch_line: LeU64::new(0),
            buffer: [BeU16::new(0); 32],
            buffer_pos: 32,
        }
    }
}

impl<M: CacheFetch> InsnCache<M> {
    pub fn reposition_after_jump(&self, phys_ip: LeU64) -> CPUResult<()> {
        self.buffer_pos = ((phys_ip.get() >> 1) & 31) as usize;
        if self.fetch_line != (phys_ip >> 6) {
            self.fetch_line = phys_ip >> 6;
            let line = match self.l1icache.read_line(self.fetch_line) {
                Ok((line, _)) => line,
                Err(CacheAccessError::Exception(ex)) => return Err(ex),
                Err(CacheAccessError::Locked) => {
                    match self.l1icache.read_line_without_probe(self.fetch_line) {
                        Ok((line, _)) => line,
                        Err(CacheAccessError::Exception(ex)) => return Err(ex),
                        Err(CacheAccessError::Locked) => {
                            let mut line = CacheLine::zeroed();

                            for i in (0usize..128).chain(core::iter::repeat(128)) {
                                match self.l1icache.read_line(self.fetch_line) {
                                    Ok((l, _)) => line = l,
                                    Err(CacheAccessError::Exception(ex)) => return Err(ex),
                                    Err(CacheAccessError::Locked) => {
                                        if i < 16 {
                                            core::hint::spin_loop()
                                        } else if i < 128 {
                                            std::thread::yield_now()
                                        } else {
                                            self.l1icache.park_on_line_unlock(self.fetch_line)
                                        }
                                    }
                                    Err(e) => unreachable!("Should not be generated {:?}", e),
                                }
                            }

                            line
                        }
                        Err(e) => unreachable!("Should not be generated {:?}", e),
                    }
                }
                Err(e) => unreachable!("Should not be generated {:?}", e),
            };

            self.buffer = bytemuck::cast(line);
        }

        Ok(())
    }
}

pub struct Cpu {
    l2cache: Rc<LocalMemoryBus>,
    l1dcache: DataCache<LocalMemory<Rc<LocalMemoryBus>>>,
}
