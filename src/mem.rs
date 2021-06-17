use std::{
    alloc::Layout,
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use bytemuck::{Pod, Zeroable};

use parking_lot::{RwLock, RwLockUpgradableReadGuard};

use crate::error::{AccessKind, CPUException, CPUResult, FaultCharacteristics};

#[repr(C, align(4096))]
#[derive(Copy, Clone, Hash, Zeroable, Pod)]
pub struct Page(pub [u8; 4096]);

pub struct MemoryController {
    mem: RwLock<HashMap<u32, Box<Page>>>,
}

impl MemoryController {
    fn allocate(htab: &mut HashMap<u32, Box<Page>>, page: u32) -> CPUResult<()> {
        // SAFETY: size_of::<Page>()==4096
        let ptr = unsafe { std::alloc::alloc_zeroed(Layout::new::<Page>()) };

        if ptr.is_null() {
            Err(CPUException::PageFault(
                (page as i64) << 12,
                FaultCharacteristics {
                    pref: (page as i64) << 12,
                    flevel: 0,
                    access_kind: AccessKind::Allocate,
                    ..Zeroable::zeroed()
                },
            ))
        } else {
            // SAFETY: Page is allocated using the global allocator above
            // ptr is not null be by the above check
            // and ptr is not used after this point
            let ptr = unsafe { Box::from_raw(ptr as *mut Page) };

            htab.insert(page, ptr);
            Ok(())
        }
    }

    pub fn new() -> Self {
        Self {
            mem: RwLock::new(HashMap::new()),
        }
    }

    pub fn read_bytes(&self, mut out: &mut [u8], paddr: u64) -> CPUResult<()> {
        if paddr > (u32::MAX as u64) {
            Err(CPUException::PageFault(
                paddr as i64,
                FaultCharacteristics {
                    pref: paddr as i64,
                    flevel: 0,
                    access_kind: AccessKind::Allocate,
                    ..Zeroable::zeroed()
                },
            ))
        } else {
            let addr = paddr as u32;
            let mut npg = addr >> 12;
            let mut off_in_pg = (addr & 0xfff) as usize;
            while !out.is_empty() {
                let guard = self.mem.upgradable_read();
                if let Some(pg) = guard.get(&npg) {
                    let bytes = &pg.0[off_in_pg..];
                    if bytes.len() < out.len() {
                        let (out1, out2) = out.split_at_mut(bytes.len());
                        out1.copy_from_slice(bytes);
                        out = out2;
                        npg += 1;
                        off_in_pg = 0;
                    } else {
                        let len = out.len();
                        out.copy_from_slice(&bytes[..len]);
                        out = &mut out[len..];
                    }
                } else {
                    let mut guard = RwLockUpgradableReadGuard::upgrade(guard);
                    if !guard.contains_key(&npg) {
                        Self::allocate(&mut guard, npg)?;
                    }
                }
            }
            Ok(())
        }
    }

    pub fn write_bytes(&mut self, mut inbytes: &[u8], paddr: u64) -> CPUResult<()> {
        if paddr > (u32::MAX as u64) {
            Err(CPUException::PageFault(
                paddr as i64,
                FaultCharacteristics {
                    pref: paddr as i64,
                    flevel: 0,
                    access_kind: AccessKind::Allocate,
                    ..Zeroable::zeroed()
                },
            ))
        } else {
            let addr = paddr as u32;
            let mut npg = addr >> 12;
            let mut off_in_pg = (addr & 0xfff) as usize;
            while !inbytes.is_empty() {
                let guard = self.mem.get_mut();
                if let Some(pg) = guard.get_mut(&npg) {
                    let bytes = &mut pg.0[off_in_pg..];
                    if bytes.len() < inbytes.len() {
                        let (in1, in2) = inbytes.split_at(bytes.len());
                        bytes.copy_from_slice(in1);
                        inbytes = in2;
                        npg += 1;
                        off_in_pg = 0;
                    } else {
                        let len = inbytes.len();
                        bytes[..len].copy_from_slice(inbytes);
                        inbytes = &inbytes[len..];
                    }
                } else {
                    if !guard.contains_key(&npg) {
                        Self::allocate(guard, npg)?;
                    }
                }
            }
            Ok(())
        }
    }

    pub fn read<T: Pod>(&self, paddr: u64) -> CPUResult<T> {
        let mut out = T::zeroed();

        self.read_bytes(bytemuck::bytes_of_mut(&mut out), paddr)?;

        Ok(out)
    }

    pub fn write<T: Pod>(&mut self, value: T, paddr: u64) -> CPUResult<()> {
        self.write_bytes(bytemuck::bytes_of(&value), paddr)
    }
}

pub struct MemoryBus {
    mem: RwLock<MemoryController>,
}

impl MemoryBus {
    pub fn new() -> Self {
        Self {
            mem: RwLock::new(MemoryController::new()),
        }
    }

    pub fn with_unlocked_bus<U, F: FnOnce(&MemoryController) -> U>(&self, f: F) -> U {
        (f)(&self.mem.read())
    }

    pub fn with_locked_bus<U, F: FnOnce(&mut MemoryController) -> U>(&self, f: F) -> U {
        (f)(&mut self.mem.write())
    }

    pub fn get_mut(&mut self) -> &mut MemoryController {
        self.mem.get_mut()
    }
}
