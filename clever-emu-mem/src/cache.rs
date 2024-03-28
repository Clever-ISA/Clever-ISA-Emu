use clever_emu_primitives::primitive::*;

use bytemuck::{Pod, Zeroable};
use lru_time_cache::LruCache;
use std::rc::Rc;
use std::sync::Arc;

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum CacheAccessError {
    NoMem,
    Locked,
    NotPresent,
    Unavail,
}

pub type CacheAccessResult<T> = Result<(T, Status), CacheAccessError>;

pub trait CacheInvalidate {
    /// Invalidates a given cache line recursively.
    ///
    /// This function requires a physical address of a cache line. It is a logic error to pass an address that is not aligned to [`CacheLine::SIZE`]
    fn invalidate(&self, line: LeU64);
    /// Invalidates the entire cache recursively.
    fn invalidate_all(&self);
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for &T {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for &mut T {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for Arc<T> {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for Rc<T> {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

impl<T: CacheInvalidate + ?Sized> CacheInvalidate for Box<T> {
    fn invalidate(&self, line: LeU64) {
        (**self).invalidate(line)
    }
    fn invalidate_all(&self) {
        (**self).invalidate_all()
    }
}

pub trait CacheFetch {
    /// Indicates whether or not the [`CacheFetch::probe_attrs`] should be called by higher level caches only if the operation is not fulfilled by that cache level.
    fn probe_on_miss_only(&self) -> bool {
        false
    }

    /// Probes the cache for the attributes of the specified cache line.
    /// The attributes includes information about the current cache state, as well as whether the cache line is locked.
    ///
    /// This function requires a physical address of a cache line. It is a logic error to pass an address that is not aligned to [`CacheLine::SIZE`]
    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs>;

    /// Attempts to read the value of the designated cache line. This willl do an attribute probe of lower level cache lines,
    /// to ensure that the line is not locked prior to the access.
    ///
    /// This function requires a physical address of a cache line. It is a logic error to pass an address that is not aligned to [`CacheLine::SIZE`]
    fn read_line(&self, line: LeU64) -> CacheAccessResult<CacheLine>;

    /// Attempts to read the value of the designated cache line. This may skip a line lock check if the read access is a hit.
    /// This is intended to be more efficient for operations that may not need complete coherency, such as instruction fetches or address translation.
    /// It is not guaranteed that any implementation of the trait will skip the line lock check, even if the access would hit.
    /// The correctness of any algorithm must not depend on not returning [`CacheAccessError::Locked`] in any case.
    ///
    /// This function requires a physical address of a cache line. It is a logic error to pass an address that is not aligned to [`CacheLine::SIZE`]
    fn read_line_weak(&self, line: LeU64) -> CacheAccessResult<CacheLine> {
        self.read_line(line)
    }

    /// Optimistically pauses the thread while the cache line lock is held.
    /// This function may return spuriously but is guaranteed to return when a corresponding call to [`CacheWrite::unlock`] is made.
    ///
    /// This function requires a physical address of a cache line. It is a logic error to pass an address that is not aligned to [`CacheLine::SIZE`]
    fn park_on_line_unlock(&self, line: LeU64);
}

pub trait CacheWrite: CacheFetch {
    /// Writes the given value to the designated cache line.
    ///
    /// A call to [`CacheWrite::write_line`] typically requires the cache line be locked, and will return [`CacheAccessError::Unavail`] if it is not.
    ///
    /// This function requires a physical address of a cache line. It is a logic error to pass an address that is not aligned to [`CacheLine::SIZE`]
    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()>;
    /// Attempts to establish the exclusive access lock to the given cache line, returning [`CacheAccessError::Locked`] if it is already locked.
    /// Until the corresponding call to [`CacheWrite::unlock`], the cache line will be locked.
    ///
    /// This function requires a physical address of a cache line. It is a logic error to pass an address that is not aligned to [`CacheLine::SIZE`]
    fn lock(&self, line: LeU64) -> CacheAccessResult<()>;
    /// Unlocks the exclusive access lock on the given cache line if it is owned, returning [`CacheAccessError::Unavail`] otherwise.
    /// This will unpark all threads waiting on [`CacheFetch::park_on_line_unlock`] for the same cache line.
    ///
    /// This function requires a physical address of a cache line. It is a logic error to pass an address that is not aligned to [`CacheLine::SIZE`]
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()>;
}

impl<T: CacheFetch + ?Sized> CacheFetch for &T {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }

    fn read_line_weak(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }

    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for &T {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

impl<T: CacheFetch + ?Sized> CacheFetch for Arc<T> {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn read_line_weak(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for Arc<T> {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

impl<T: CacheFetch + ?Sized> CacheFetch for Rc<T> {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line_weak(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for Rc<T> {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

impl<T: CacheFetch + ?Sized> CacheFetch for Box<T> {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line_weak(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for Box<T> {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

impl<T: CacheFetch + ?Sized> CacheFetch for &mut T {
    fn probe_on_miss_only(&self) -> bool {
        (**self).probe_on_miss_only()
    }

    fn probe_attrs(&self, line: LeU64) -> CacheAccessResult<CacheAttrs> {
        (**self).probe_attrs(line)
    }

    fn read_line_weak(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }

    fn read_line(&self, val: LeU64) -> CacheAccessResult<CacheLine> {
        (**self).read_line(val)
    }
    fn park_on_line_unlock(&self, line: LeU64) {
        (**self).park_on_line_unlock(line)
    }
}

impl<T: CacheWrite + ?Sized> CacheWrite for &mut T {
    fn lock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).lock(line)
    }
    fn unlock(&self, line: LeU64) -> CacheAccessResult<()> {
        (**self).unlock(line)
    }

    fn write_line(&self, line: LeU64, val: CacheLine) -> CacheAccessResult<()> {
        (**self).write_line(line, val)
    }
}

#[repr(C, align(64))]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
pub struct CacheLine([u8; 64]);

impl CacheLine {
    pub const SIZE: usize = core::mem::size_of::<Self>();
}

#[repr(C, align(8))]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Pod, Zeroable)]
pub struct CacheAttrs {
    seq_lock: LeU64,
}

impl CacheAttrs {
    pub const fn is_locked(&self) -> bool {
        (self.seq_lock.get() & 1) != 0
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Status {
    Hit,
    Miss,
}

impl core::ops::BitAnd for Status {
    type Output = Status;
    fn bitand(self, other: Self) -> Self {
        match (self, other) {
            (Self::Hit, Self::Hit) => Self::Hit,
            _ => Self::Miss,
        }
    }
}

impl core::ops::BitAndAssign for Status {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

pub struct Cache(LruCache<LeU64, (CacheLine, CacheAttrs)>);

impl Cache {
    pub fn new(size: usize) -> Self {
        Self(LruCache::with_capacity(size))
    }

    pub fn invalidate_local(&mut self, line: LeU64) {
        self.0.remove(&line);
    }

    pub fn invalidate_all_local(&mut self) {
        self.0.clear();
    }

    pub fn invalidate_global<C: CacheInvalidate + ?Sized>(&mut self, line: LeU64, upstream: &C) {
        self.invalidate_local(line);
        upstream.invalidate(line);
    }

    pub fn invalidate_all_global<C: CacheInvalidate + ?Sized>(&mut self, upstream: &C) {
        self.invalidate_all_local();
        upstream.invalidate_all()
    }

    pub fn probe_attrs<C: CacheFetch + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<CacheAttrs> {
        if let Some((_, attrs)) = self.0.get(&line) {
            if upstream.probe_on_miss_only() {
                Ok((*attrs, Status::Hit))
            } else {
                let (new_attrs, _) = upstream.probe_attrs(line)?;
                if attrs.seq_lock == (new_attrs.seq_lock & !1) {
                    Ok((*attrs, Status::Hit))
                } else if new_attrs.seq_lock & 1 != 0 {
                    Err(CacheAccessError::Locked)
                } else {
                    let (val, _) = upstream.read_line(line)?;
                    self.0.insert(line, (val, new_attrs));

                    Ok((new_attrs, Status::Miss))
                }
            }
        } else {
            let (attrs, _) = upstream.probe_attrs(line)?;
            if attrs.seq_lock & 1 != 0 {
                Err(CacheAccessError::Locked)
            } else {
                let (val, _) = upstream.read_line(line)?;
                self.0.insert(line, (val, attrs));

                Ok((attrs, Status::Miss))
            }
        }
    }

    pub fn read_line_without_probe<C: CacheFetch + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<CacheLine> {
        if let Some((line, _)) = self.0.get(&line) {
            Ok((*line, Status::Hit))
        } else {
            self.read_line(line, upstream)
        }
    }

    pub fn read_line<C: CacheFetch + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<CacheLine> {
        let (_, status) = self.probe_attrs(line, upstream)?; // we don't need to know the attrs, but this fetches from upstream when needed.

        let (line, _) = self
            .0
            .get(&line)
            .expect("We just probed this line, what do you mean we don't have it's content");

        Ok((*line, status))
    }

    pub fn write_line<C: CacheWrite + ?Sized>(
        &mut self,
        line: LeU64,
        val: CacheLine,
        upstream: &C,
    ) -> CacheAccessResult<()> {
        let (attrs, status) = self.probe_attrs(line, upstream)?;
        if (attrs.seq_lock & 1) == 0 {
            return Err(CacheAccessError::Unavail);
        }
        let (line_val, _) = self
            .0
            .get_mut(&line)
            .expect("We just probed this line, what do you mean we don't have it's content");

        *line_val = val;

        upstream.write_line(line, val)?;

        Ok(((), status))
    }

    pub fn lock<C: CacheWrite + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<()> {
        let (mut attrs, status) = self.probe_attrs(line, upstream)?;

        if (attrs.seq_lock & 1) == 0 {
            upstream.lock(line)?;
            attrs.seq_lock |= 1;
            let (_, line_attrs) = self
                .0
                .get_mut(&line)
                .expect("We just probed this line, what do you mean we don't have it's content");
            *line_attrs = attrs;
            Ok(((), status))
        } else {
            Err(CacheAccessError::Locked)
        }
    }

    pub fn unlock<C: CacheWrite + ?Sized>(
        &mut self,
        line: LeU64,
        upstream: &C,
    ) -> CacheAccessResult<()> {
        let (mut attrs, status) = self.probe_attrs(line, upstream)?;

        if (attrs.seq_lock & 1) == 1 {
            upstream.unlock(line)?;
            attrs.seq_lock += 1;
            let (_, line_attrs) = self
                .0
                .get_mut(&line)
                .expect("We just probed this line, what do you mean we don't have it's content");
            *line_attrs = attrs;
            Ok(((), status))
        } else {
            Err(CacheAccessError::Unavail)
        }
    }
}
