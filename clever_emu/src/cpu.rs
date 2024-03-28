pub mod cpuid;
pub mod reg;
pub mod state;
pub mod ucode;

use std::cell::{Cell, RefCell};
use std::mem::MaybeUninit;
use std::rc::Rc;

use crate::error::{self, CPUResult, FaultStatus};
use crate::error::{CPUException, FaultCharacteristics};
use crate::mem::{
    Cache, CacheAccessError, CacheAccessResult, CacheAttrs, CacheFetch, CacheInvalidate, CacheLine,
    CacheWrite, LocalMemory, LocalMemoryBus, Status,
};
use crate::page::*;
use crate::primitive::*;

use bytemuck::{Pod, Zeroable};
use lru_time_cache::LruCache;

use crate::util::*;

use crate::bitfield::{bitfield, DisplayBitfield, FromBitfield, Sentinel};

use self::reg::Regs;
use self::state::RandUnit;
use self::ucode::UCodeRom;

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

struct ICacheBuffer {
    fetch_line: LeU64,
    buffer: [BeU16; 32],
}

pub struct InsnCache<M> {
    l1icache: LocalMemory<M>,
    buffer: RefCell<ICacheBuffer>,
    buffer_pos: Cell<usize>,
}

impl ICacheBuffer {
    const fn new() -> Self {
        Self {
            fetch_line: LeU64::new(0),
            buffer: [BeU16::new(0); 32],
        }
    }
    fn read_full_line_blocking<M: CacheFetch>(&mut self, mem: &M) -> CPUResult<()> {
        let mut line = CacheLine::zeroed();

        for i in (0usize..128).chain(core::iter::repeat(128)) {
            match mem.read_line(self.fetch_line) {
                Ok((l, _)) => line = l,
                Err(CacheAccessError::Exception(ex)) => return Err(ex),
                Err(CacheAccessError::Locked) => {
                    if i < 16 {
                        core::hint::spin_loop()
                    } else if i < 128 {
                        std::thread::yield_now()
                    } else {
                        mem.park_on_line_unlock(self.fetch_line)
                    }
                }
                Err(e) => unreachable!("Should not be generated {:?}", e),
            }
        }

        self.buffer = bytemuck::cast(line);

        Ok(())
    }
    fn read_full_line<M: CacheFetch>(&mut self, mem: &M) -> CPUResult<()> {
        let line = match mem.read_line(self.fetch_line) {
            Ok((line, _)) => Ok(line),
            Err(CacheAccessError::Exception(ex)) => Err(ex),
            Err(CacheAccessError::Locked) => match mem.read_line(self.fetch_line) {
                Ok((line, _)) => Ok(line),
                Err(CacheAccessError::Exception(ex)) => Err(ex),
                Err(CacheAccessError::Locked) => return self.read_full_line_blocking(mem),
                Err(e) => unreachable!("Should not be generated {:?}", e),
            },
            Err(e) => unreachable!("Should not be generated {:?}", e),
        }?;

        self.buffer = bytemuck::cast(line);

        Ok(())
    }
}

impl<M> InsnCache<M> {
    pub fn new(underlying: M, l1isize: usize) -> Self {
        Self {
            l1icache: LocalMemory::new(underlying, l1isize),
            buffer: RefCell::new(ICacheBuffer::new()),
            buffer_pos: Cell::new(32),
        }
    }
}

impl<M: CacheFetch> InsnCache<M> {
    pub fn reposition_after_jump(&self, phys_ip: LeU64) -> CPUResult<()> {
        self.buffer_pos.set(((phys_ip.get() >> 1) & 31) as usize);
        let fetch_line = self.buffer.borrow().fetch_line;
        if fetch_line != (phys_ip >> 6) {
            let mut buffer = self.buffer.borrow_mut();
            buffer.fetch_line = phys_ip >> 6;

            buffer.read_full_line(&self.l1icache)?;
        }

        Ok(())
    }

    pub fn reposition_after_page_boundary(&self, pg: LeU64) -> CPUResult<()> {
        self.buffer_pos.set(0);
        let fetch_line = self.buffer.borrow().fetch_line;
        if fetch_line != (pg >> 6) {
            let mut buffer = self.buffer.borrow_mut();
            buffer.fetch_line = pg >> 6;

            buffer.read_full_line(&self.l1icache)?;
        }
        Ok(())
    }

    pub fn fetch(&self) -> CPUResult<BeU16> {
        let pos = self.buffer_pos.get();
        let pos_next = pos + 1;
        let overflow = (pos_next >> 5) != 0;
        self.buffer_pos.set(pos_next & 31);
        if overflow {
            let mut buffer = self.buffer.borrow_mut();
            buffer.fetch_line += 1;
            buffer.read_full_line(&self.l1icache)?;
        }
        let val = self.buffer.borrow().buffer[pos_next & 31];

        Ok(val)
    }
}

pub struct TlbBuffer {
    backing: LruCache<LeI64, (PageEntry, CpuExecutionMode)>,
}

impl TlbBuffer {
    pub fn new(tlb_entry_count: usize) -> Self {
        Self {
            backing: LruCache::with_capacity(tlb_entry_count),
        }
    }

    pub fn resolve_addr<M: CacheFetch>(
        &mut self,
        mem: &M,
        ptbl: LeU64,
        vaddr: LeI64,
        xm: CpuExecutionMode,
        mut init_chars: FaultCharacteristics,
    ) -> CPUResult<PageEntry> {
        let vpage = vaddr >> 12;
        if let Some((val, req)) = self.backing.get(&vpage) {
            if *req < xm {
                init_chars.flevel = LeU8::new(0);
                init_chars.pref = val.bits();
                init_chars.status |= FaultStatus::with_nested(true);
                Err(CPUException::PageFault(vaddr, init_chars))
            } else {
                Ok(*val)
            }
        } else {
            let mut paged_addr = vaddr.get();
            let ptl = (ptbl & 7).get() as u32;

            let mut addr_bits = 32 + ptl * 8;

            let lead_bits = vaddr.leading_zeros() + vaddr.leading_ones();

            if lead_bits < (65 - addr_bits) {
                // Unused address bits must be copies of most significant bits

                init_chars.flevel = LeU8::new(0);
                init_chars.status |= FaultStatus::with_non_canonical(true);
                return Err(CPUException::PageFault(vaddr, init_chars));
            }

            addr_bits -= 9;

            let mut tail = addr_bits % 12;
            if tail == 0 {
                tail = 12;
            }
            paged_addr = paged_addr.rotate_left(tail as u32);
            addr_bits -= tail;
            let mut bits = paged_addr & ((1 << tail) - 1);
            let mut pe = ptbl & 4095;
            let mut pg_mode = CpuExecutionMode::User;
            loop {
                let addr = pe | ((bits as u64) << 3);
                let offset = ((addr.get() & 0x3F) >> 3) as usize;
                let line_addr = addr & !0x3F;

                let line = match mem.read_line(line_addr) {
                    Ok((line, _)) => line,
                    Err(CacheAccessError::Exception(ex)) => return Err(ex),
                    Err(CacheAccessError::Locked) => {
                        let mut line = CacheLine::zeroed();
                        for i in (0usize..).take(128).chain(core::iter::repeat(128)) {
                            match mem.read_line(line_addr) {
                                Ok((le, status)) => line = le,
                                Err(CacheAccessError::Exception(ex)) => return Err(ex),
                                Err(CacheAccessError::Locked) => {
                                    if i < 16 {
                                        core::hint::spin_loop()
                                    } else if i < 128 {
                                        std::thread::yield_now()
                                    } else {
                                        mem.park_on_line_unlock(line_addr)
                                    }
                                }
                                Err(e) => unreachable!("Should not be generated {:?}", e),
                            }
                        }
                        line
                    }
                    Err(e) => unreachable!("Should not be generated {:?}", e),
                };

                let entries: [PageEntry; CacheLine::SIZE >> 3] = bytemuck::cast(line);
                let entry = entries[offset];
                pe = entry.addr();
                let flags = entry.flags();

                if !flags.validate() {
                    init_chars.pref = entry.bits();
                    init_chars.status |= FaultStatus::with_validation_error(true);
                    break;
                }

                if addr_bits != 0 {
                    if !entry.npe_flags().validate() {
                        init_chars.pref = entry.bits();
                        init_chars.status |= FaultStatus::with_validation_error(true);
                        break;
                    }
                }

                if flags.perm() == 0 {
                    init_chars.pref = entry.bits();
                    break;
                }
                let mode = flags.xm().xm();
                if mode < xm {
                    init_chars.pref = entry.bits();
                    init_chars.status |= FaultStatus::with_validation_error(true);
                    break;
                }

                if mode < pg_mode {
                    pg_mode = mode;
                }

                if addr_bits == 0 {
                    self.backing.insert(vpage, (entry, pg_mode));
                    return Ok(entry);
                }
            }

            if addr_bits != 0 {
                init_chars.status |= FaultStatus::with_nested(true);
            }

            init_chars.flevel = LeU8::new((addr_bits / 12) as u8);

            Err(CPUException::PageFault(vaddr, init_chars))
        }
    }

    pub fn flush_after_update(&mut self) {
        self.backing.clear()
    }
}

pub struct AddrResolver<M> {
    buffer: RefCell<TlbBuffer>,
    mem: M,
    ptbl: LeU64,
}

impl<M> AddrResolver<M> {
    pub fn new(mem: M, buffer_size: usize) -> Self {
        AddrResolver {
            mem,
            buffer: RefCell::new(TlbBuffer::new(buffer_size)),
            ptbl: LeU64::new(0),
        }
    }

    pub fn set_ptbl(&mut self, ptbl: LeU64) {
        self.ptbl = ptbl;
        self.buffer.get_mut().flush_after_update();
    }
}

impl<M: CacheFetch> AddrResolver<M> {
    pub fn resolve_addr(
        &self,
        vaddr: LeI64,
        xm: CpuExecutionMode,
        init_chars: FaultCharacteristics,
    ) -> CPUResult<PageEntry> {
        self.buffer
            .borrow_mut()
            .resolve_addr(&self.mem, self.ptbl, vaddr, xm, init_chars)
    }
}

pub struct Cpu<'a> {
    l2cache: Rc<LocalMemoryBus>,
    l1dcache: DataCache<Rc<LocalMemoryBus>>,
    l1icache: InsnCache<Rc<LocalMemoryBus>>,
    addr_resolver: AddrResolver<Rc<LocalMemoryBus>>,
    regs: Regs,
    ucode_rom: UCodeRom<'a>,
    state: RandUnit,
    pending_exceptions: Vec<CPUException>,
}

impl<'a> Cpu<'a> {
    pub fn new(
        ucode_rom: UCodeRom<'a>,
        l2cache: Rc<LocalMemoryBus>,
        l1dsize: usize,
        l1isize: usize,
        tlb_buf_size: usize,
    ) -> Cpu {
        let l1dcache = DataCache::new(l2cache.clone(), l1dsize);
        let l1icache = InsnCache::new(l2cache.clone(), l1isize);
        let addr_resolver = AddrResolver::new(l2cache.clone(), tlb_buf_size);
        Cpu {
            l2cache,
            l1dcache,
            l1icache,
            addr_resolver,
            regs: Regs::new(),
            ucode_rom,
            state: RandUnit::new(),
            pending_exceptions: vec![],
        }
    }

    pub fn regs_mut(&mut self) -> &mut Regs {
        &mut self.regs
    }

    pub fn regs(&self) -> &Regs {
        &self.regs
    }

    pub fn init_after_reset(&mut self) {
        self.regs = Regs::new();
    }
}

pub struct CpuHolder<'a> {
    l2cache: Rc<LocalMemoryBus>,
    cpus: Vec<Cpu<'a>>,
}
