use std::{cell::RefCell, sync::Arc};

use parking_lot::Mutex;

use crate::{
    cache::{
        Cache, CacheAccessError, CacheAccessResult, CacheFetch, CacheInvalidate, CacheLine,
        CacheWrite, Status,
    },
    phys::SysMemory,
};

use clever_emu_primitives::primitive::LeU64;

pub struct SharedMemoryBus<M> {
    base: M,
    cache: Mutex<Cache>,
}

impl<M> SharedMemoryBus<M> {
    pub fn new(base: M, cache_size: usize) -> Self {
        Self {
            base,
            cache: Mutex::new(Cache::new(cache_size)),
        }
    }
}

impl<M: CacheInvalidate> CacheInvalidate for SharedMemoryBus<M> {
    fn invalidate(&self, line: LeU64) {
        let mut lock = self.cache.lock();
        lock.invalidate_global(line, &self.base)
    }

    fn invalidate_all(&self) {
        let mut lock = self.cache.lock();
        lock.invalidate_all_global(&self.base)
    }
}

impl<M: CacheFetch> CacheFetch for SharedMemoryBus<M> {
    fn probe_attrs(
        &self,
        line: LeU64,
    ) -> crate::cache::CacheAccessResult<crate::cache::CacheAttrs> {
        let mut lock = self.cache.lock();
        lock.probe_attrs(line, &self.base)
    }

    fn read_line(&self, line: LeU64) -> crate::cache::CacheAccessResult<crate::cache::CacheLine> {
        let mut lock = self.cache.lock();
        lock.read_line(line, &self.base)
    }

    fn read_line_weak(
        &self,
        line: LeU64,
    ) -> crate::cache::CacheAccessResult<crate::cache::CacheLine> {
        let mut lock = self.cache.lock();
        lock.read_line_without_probe(line, &self.base)
    }

    fn park_on_line_unlock(&self, line: LeU64) {
        self.base.park_on_line_unlock(line);
    }
}

impl<M: CacheWrite> CacheWrite for SharedMemoryBus<M> {
    fn write_line(
        &self,
        line: LeU64,
        val: crate::cache::CacheLine,
    ) -> crate::cache::CacheAccessResult<()> {
        let mut lock = self.cache.lock();
        lock.write_line(line, val, &self.base)
    }

    fn lock(&self, line: LeU64) -> crate::cache::CacheAccessResult<()> {
        let mut lock = self.cache.lock();
        lock.lock(line, &self.base)
    }

    fn unlock(&self, line: LeU64) -> crate::cache::CacheAccessResult<()> {
        let mut lock = self.cache.lock();
        lock.unlock(line, &self.base)
    }
}

pub struct LocalMemoryBus<M> {
    base: M,
    cache: RefCell<Cache>,
}

impl<M> LocalMemoryBus<M> {
    pub fn new(base: M, cache_size: usize) -> Self {
        Self {
            base,
            cache: RefCell::new(Cache::new(cache_size)),
        }
    }
}

impl<M: CacheInvalidate> CacheInvalidate for LocalMemoryBus<M> {
    fn invalidate(&self, line: LeU64) {
        let mut lock = self.cache.borrow_mut();
        lock.invalidate_global(line, &self.base)
    }

    fn invalidate_all(&self) {
        let mut lock = self.cache.borrow_mut();
        lock.invalidate_all_global(&self.base)
    }
}

impl<M: CacheFetch> LocalMemoryBus<M> {
    fn access_blocking<T, F: FnMut(&Self, LeU64) -> CacheAccessResult<T>>(
        &self,
        mut f: F,
        line: LeU64,
    ) -> CacheAccessResult<T> {
        for i in 0..128 {
            match f(self, line) {
                Ok(val) => return Ok(val),
                Err(CacheAccessError::Locked) => {
                    if i < 16 {
                        core::hint::spin_loop()
                    } else {
                        std::thread::yield_now()
                    }
                }
                Err(e) => return Err(e),
            }
        }
        loop {
            match f(self, line) {
                Ok(val) => return Ok(val),
                Err(CacheAccessError::Locked) => self.base.park_on_line_unlock(line),
                Err(e) => return Err(e),
            }
        }
    }

    /// Reads from the cache line, blocking if a lower-level cache line is locked (and this cache does not own that lock)
    pub fn read_blocking(&self, line: LeU64) -> CacheAccessResult<CacheLine> {
        self.access_blocking(|this, line| this.read_line(line), line)
    }

    /// Reads from the cache line weakly. This may block if the lower-level cache line is locked (and is not owned by this cache),
    ///  but it may bypass this check instead.
    pub fn read_weak_blocking(&self, line: LeU64) -> CacheAccessResult<CacheLine> {
        match self.read_line_weak(line) {
            Ok(val) => return Ok(val),
            Err(CacheAccessError::Locked) => self.read_blocking(line),
            Err(e) => return Err(e),
        }
    }

    pub fn read_dual_blocking(&self, line: LeU64) -> CacheAccessResult<[CacheLine; 2]> {
        let line2 = line + (CacheLine::SIZE as u64);
        let mut status = Status::Hit;

        let vals = loop {
            let (val1, status1) = self.read_blocking(line)?;
            let (val2, status2) = self.read_blocking(line2)?;

            status &= status1 & status2;

            if status2 == Status::Hit {
                break [val1, val2];
            }
        };

        Ok((vals, status))
    }
}

impl<M: CacheFetch> CacheFetch for LocalMemoryBus<M> {
    fn probe_attrs(
        &self,
        line: LeU64,
    ) -> crate::cache::CacheAccessResult<crate::cache::CacheAttrs> {
        let mut lock = self.cache.borrow_mut();
        lock.probe_attrs(line, &self.base)
    }

    fn read_line(&self, line: LeU64) -> crate::cache::CacheAccessResult<crate::cache::CacheLine> {
        let mut lock = self.cache.borrow_mut();
        lock.read_line(line, &self.base)
    }

    fn read_line_weak(
        &self,
        line: LeU64,
    ) -> crate::cache::CacheAccessResult<crate::cache::CacheLine> {
        let mut lock = self.cache.borrow_mut();
        lock.read_line_without_probe(line, &self.base)
    }

    fn park_on_line_unlock(&self, line: LeU64) {
        self.base.park_on_line_unlock(line);
    }
}

pub struct LocalMemoryLockGuard<'a, M: CacheWrite>(&'a LocalMemoryBus<M>, LeU64);

impl<'a, M: CacheWrite> Drop for LocalMemoryLockGuard<'a, M> {
    fn drop(&mut self) {
        self.0.unlock(self.1).unwrap();
    }
}

impl<M: CacheWrite> LocalMemoryBus<M> {
    /// Writes the given value to the cache line, acquiring the cache line lock (as though by [`LocalMemoryBus::lock_blocking`]) if necessary.
    pub fn write_blocking(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        match self.write_line(line, val) {
            Ok(val) => Ok(val),
            Err(CacheAccessError::Unavail) => {
                let (guard, _) = self.lock_blocking(line)?;

                self.write_line(line, val)
            }
            Err(e) => Err(e),
        }
    }

    /// Locks the cache line, blocking if it is already locked in the current cache level.
    ///
    /// The function, if it succeeds, returns a guard that unlocks the line on drop. It is a logic error to use [`LocalMemoryBus::unlock`]
    ///   to release the lock unless you first [`forget`][core::mem::forget] the guard.
    pub fn lock_blocking(&self, line: LeU64) -> CacheAccessResult<LocalMemoryLockGuard<M>> {
        self.access_blocking(|this, line| this.lock(line), line)
            .map(|(_, status)| (LocalMemoryLockGuard(self, line), status))
    }
}

impl<M: CacheWrite> CacheWrite for LocalMemoryBus<M> {
    fn write_line(
        &self,
        line: LeU64,
        val: crate::cache::CacheLine,
    ) -> crate::cache::CacheAccessResult<()> {
        let mut lock = self.cache.borrow_mut();
        lock.write_line(line, val, &self.base)
    }

    fn lock(&self, line: LeU64) -> crate::cache::CacheAccessResult<()> {
        let mut lock = self.cache.borrow_mut();
        lock.lock(line, &self.base)
    }

    fn unlock(&self, line: LeU64) -> crate::cache::CacheAccessResult<()> {
        let mut lock = self.cache.borrow_mut();
        lock.unlock(line, &self.base)
    }
}

pub type GlobalMemory = SharedMemoryBus<SysMemory>;
pub type LocalMemory = LocalMemoryBus<GlobalMemory>;
