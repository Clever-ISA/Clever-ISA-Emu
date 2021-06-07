use std::{alloc::Layout, collections::HashMap, convert::TryInto, ptr::NonNull};

use parking_lot::{
    const_rwlock, lock_api::RawRwLockRecursive, RwLock, RwLockUpgradableReadGuard, RwLockWriteGuard,
};
use tearor::TearCell;

use bytemuck::{Pod, Zeroable};

use crate::error::{AccessKind, CPUException, CPUResult, FaultCharacteristics};

pub struct MemController {
    htab: RwLock<HashMap<u32, NonNull<[TearCell<u64>; 512]>>>,
}

impl MemController {
    unsafe fn allocate(
        guard: RwLockUpgradableReadGuard<HashMap<u32, NonNull<[TearCell<u64>; 512]>>>,
        pg: u32,
    ) -> CPUResult<RwLockUpgradableReadGuard<HashMap<u32, NonNull<[TearCell<u64>; 512]>>>> {
        let mut guard = RwLockUpgradableReadGuard::upgrade(guard);
        if guard.get(&pg).is_none() {
            let block = std::alloc::alloc_zeroed(
                Layout::new::<[TearCell<u64>; 512]>()
                    .align_to(4096)
                    .unwrap(),
            )
            .cast::<[TearCell<u64>; 512]>();

            if let Some(b) = NonNull::new(block) {
                guard.insert(pg, b);
            } else {
                return Err(CPUException::PageFault(
                    (pg as i64) << 12,
                    FaultCharacteristics {
                        pref: (pg as i64) << 12,
                        flevel: 0,
                        access_kind: AccessKind::Access,
                        ..Zeroable::zeroed()
                    },
                ));
            }
        }
        Ok(RwLockWriteGuard::downgrade_to_upgradable(guard))
    }

    pub fn new() -> MemController {
        MemController {
            htab: RwLock::new(HashMap::new()),
        }
    }

    pub fn read_bytes(&self, paddr: u64, mut out: &mut [u8]) -> CPUResult<()> {
        if paddr > (u32::MAX as u64) {
            return Err(CPUException::PageFault(
                paddr as i64,
                FaultCharacteristics {
                    pref: (paddr as i64) & !0xfff,
                    flevel: 0,
                    access_kind: AccessKind::Access,
                    ..Zeroable::zeroed()
                },
            ));
        }

        let page = (paddr >> 12) as u32;
        let idx_in_page = (paddr & 0xfff) as usize >> 3;
        let off = (paddr & 0x7) as usize;
        let htab = self.htab.upgradable_read();
        if let Some(&b) = htab.get(&page) {
            let bytes = &unsafe { b.as_ref() }[idx_in_page..];
            let len = if out.len() & 0x7 != 0 {
                out.len() >> 3 + 1
            } else {
                out.len() >> 3
            };
            if let Some(mut bytes) = bytes.get(..len) {
                if out.len() < (8 - off) & 0x7 {
                    let val = bytes[0].load() >> off;
                    out.copy_from_slice(&val.to_le_bytes()[..out.len()]);
                    out = &mut [];
                } else if off != 0 {
                    let val = bytes[0].load() >> off;
                    out.copy_from_slice(&val.to_le_bytes()[..(8 - off)]);
                    out = &mut out[(8 - off)..];
                }
                while out.len() != 0 {
                    if out.len() < 8 {
                        let val = bytes[0].load();
                        out.copy_from_slice(&val.to_le_bytes()[..out.len()]);
                        out = &mut [];
                    } else {
                        let val = bytes[0].load();
                        bytes = &bytes[1..];
                        out[..8].copy_from_slice(&val.to_le_bytes());
                        out = &mut out[8..];
                    }
                }
            } else {
                let len = bytes.len() << 3;
                drop(bytes);
                drop(htab);
                self.read_bytes(paddr, &mut out[..len])?;
                self.read_bytes((paddr & !0xfff) + 0x1000, &mut out[len..])?;
            }
        } else {
            let _ = unsafe { MemController::allocate(htab, page)? }; // Drop
            self.read_bytes(paddr, out)?;
        }

        Ok(())
    }

    pub fn write_bytes(&self, paddr: u64, mut in_bytes: &[u8]) -> CPUResult<()> {
        if paddr > (u32::MAX as u64) {
            return Err(CPUException::PageFault(
                paddr as i64,
                FaultCharacteristics {
                    pref: (paddr as i64) & !0xfff,
                    flevel: 0,
                    access_kind: AccessKind::Access,
                    ..Zeroable::zeroed()
                },
            ));
        }

        let page = (paddr >> 12) as u32;
        let idx_in_page = (paddr & 0xfff) as usize >> 3;
        let off = (paddr & 0x7) as usize;
        let htab = self.htab.upgradable_read();
        if let Some(&b) = htab.get(&page) {
            let bytes = &unsafe { b.as_ref() }[idx_in_page..];
            let len = if in_bytes.len() & 0x7 != 0 {
                in_bytes.len() >> 3 + 1
            } else {
                in_bytes.len() >> 3
            };
            if let Some(mut bytes) = bytes.get(..len) {
                if in_bytes.len() < (8 - off) & 0x7 {
                    let mut vbytes = bytes[0].load().to_le_bytes();
                    vbytes[off..].copy_from_slice(in_bytes);
                    bytes[0].store(u64::from_le_bytes(vbytes));
                    in_bytes = &[];
                    bytes = &bytes[1..];
                } else if off != 0 {
                    let mut vbytes = bytes[0].load().to_le_bytes();
                    vbytes[off..].copy_from_slice(in_bytes);
                    bytes[0].store(u64::from_le_bytes(vbytes));
                    in_bytes = &in_bytes[(8 - off)..];
                    bytes = &bytes[1..];
                }
                while in_bytes.len() != 0 {
                    if in_bytes.len() < 8 {
                        let mut vbytes = bytes[0].load().to_le_bytes();
                        vbytes[..in_bytes.len()].copy_from_slice(in_bytes);
                        bytes[0].store(u64::from_le_bytes(vbytes));
                        in_bytes = &[];
                        bytes = &bytes[1..];
                    } else {
                        let vbytes = in_bytes[..8].try_into().unwrap();
                        bytes[0].store(u64::from_le_bytes(vbytes));
                        in_bytes = &in_bytes[8..];
                        bytes = &bytes[1..];
                    }
                }
            } else {
                let len = bytes.len() << 3;
                drop(bytes);
                drop(htab);
                self.write_bytes(paddr, &in_bytes[..len])?;
                self.write_bytes((paddr & !0xfff) + 0x1000, &in_bytes[len..])?;
            }
        } else {
            let _ = unsafe { MemController::allocate(htab, page)? }; // Drop
            self.write_bytes(paddr, in_bytes)?;
        }

        Ok(())
    }

    pub fn read<T: Pod>(&self, paddr: u64) -> CPUResult<T> {
        let mut ret = T::zeroed();

        self.read_bytes(
            paddr,
            bytemuck::cast_slice_mut(core::slice::from_mut(&mut ret)),
        )?;

        Ok(ret)
    }

    pub fn write<T: Pod>(&self, paddr: u64, val: T) -> CPUResult<()> {
        self.write_bytes(paddr, bytemuck::cast_slice(core::slice::from_ref(&val)))
    }
}

pub struct MemBus {
    ctrl: RwLock<MemController>,
}

impl MemBus {
    pub fn new() -> MemBus {
        MemBus {
            ctrl: RwLock::new(MemController::new()),
        }
    }

    pub fn with_locked_bus<T, F: FnOnce(&MemController) -> CPUResult<T>>(
        &self,
        f: F,
    ) -> CPUResult<T> {
        f(&self.ctrl.write())
    }

    pub fn read_bytes(&self, paddr: u64, out: &mut [u8]) -> CPUResult<()> {
        self.ctrl.read().read_bytes(paddr, out)
    }

    pub fn write_bytes(&self, paddr: u64, in_bytes: &[u8]) -> CPUResult<()> {
        self.ctrl.read().write_bytes(paddr, in_bytes)
    }

    pub fn read<T: Pod>(&self, paddr: u64) -> CPUResult<T> {
        let mut ret = T::zeroed();

        self.read_bytes(
            paddr,
            bytemuck::cast_slice_mut(core::slice::from_mut(&mut ret)),
        )?;

        Ok(ret)
    }

    pub fn write<T: Pod>(&self, paddr: u64, val: T) -> CPUResult<()> {
        self.write_bytes(paddr, bytemuck::cast_slice(core::slice::from_ref(&val)))
    }
}
