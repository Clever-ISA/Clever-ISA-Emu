use bytemuck::{Pod, Zeroable};
use clever_emu_primitives::{
    const_transmute_safe, const_zeroed_safe, primitive::LeU64, size_of_as_u64,
};

use clever_emu_mem::{
    cache::{CacheFetch, CacheLine, Status},
    io::IoPort,
    phys::{Page, SysMemory},
};

use crate::store::Storage;
use std::sync::Arc;

#[repr(C, align(32))] // aligned in physical memory
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Zeroable, Pod)]
pub struct DmaReq {
    /// **Physical** address of the destination/source memory
    pub paddr: LeU64,
    /// Length of memory to write to.
    /// Due to limitations, may cause issues if this exceeds a page in size
    pub len: LeU64,
    /// Offset of the drive to read from. Does not support over-large (more than 2^64 byte) volumes
    pub diskoff: LeU64,
    /// Which drive is identified and flags
    ///
    /// Bits:
    /// * Bit 0: Direction Bit (0=Read from Device, 1=Write to Device)
    /// * Bits 1-31: Reserved
    /// * Bits 32-63: Device Id in dma space
    pub disk_id_and_flags: LeU64,
}

#[derive(Default)]
pub struct InterfaceIodma {
    attached: Vec<Box<dyn Storage + Sync>>,
    memory: Option<Arc<SysMemory>>,
}

impl InterfaceIodma {
    pub const fn new() -> Self {
        Self {
            attached: Vec::new(),
            memory: None,
        }
    }

    pub fn set_memory_bus(&mut self, memory: Arc<SysMemory>) {
        self.memory = Some(memory);
    }

    pub fn attach_dyn(&mut self, storage: Box<dyn Storage + Sync + 'static>) {
        if u32::try_from(self.attached.len()).is_err() {
            panic!("We cannot have more than 4 Billion attached devices at once")
        }
        self.attached.push(storage)
    }
    pub fn attach<T: Storage + Sync + 'static>(&mut self, storage: T) {
        self.attach_dyn(Box::new(storage))
    }
}

impl IoPort for InterfaceIodma {
    fn responds_to_port_addr(&self, addr: LeU64) -> bool {
        addr == LeU64::new(0x100000001)
    }

    fn port_in(&self, addr: LeU64, size: clever_emu_types::SizeControl) -> LeU64 {
        LeU64::new(self.attached.len() as u64) & size.as_regwidth_mask()
    }

    fn port_out(&self, addr: LeU64, data: LeU64, size: clever_emu_types::SizeControl) {
        let memory = self.memory.as_deref().unwrap();
        let req_addr = data & !(size_of_as_u64::<DmaReq>() as u64 - 1);

        let req_offset =
            (req_addr & (CacheLine::SIZE - 1)) >> (size_of_as_u64::<DmaReq>().trailing_zeros());

        let (line, _) = memory
            .read_line_weak(req_addr)
            .unwrap_or_else(|_| (const_zeroed_safe(), Status::Miss));

        let reqs: [DmaReq; size_of::<CacheLine>() / size_of::<DmaReq>()] =
            const_transmute_safe(line);

        let DmaReq {
            mut paddr,
            mut len,
            diskoff,
            disk_id_and_flags,
        } = reqs[req_offset.get() as usize];

        let disk_id = (disk_id_and_flags >> 32).get() as usize;

        if let Some(storage) = self.attached.get(disk_id) {
            let mut offset = diskoff.get();

            // Optimize large accesses by doing them page-at-a-time rather than cache-line at a time
            // As a consequence we lose cache-line coherency, but only can tear at the cache-line level
            //
            // Because we access the System Memory Directly, we also don't necessarily cause subsequent reads to see the data we write.
            // This can be fixed by invalidating the affected cache lines with a `dflush` instruction
            let first_page_offset = (paddr & (size_of_as_u64::<Page>() - 1)).get() as usize;
            let first_page_tail_len = size_of_as_u64::<Page>() - (first_page_offset as u64);
            let first_page = (paddr & !(size_of_as_u64::<Page>() - 1)) >> 12;

            let Ok(first_page) = first_page.try_into() else {
                return;
            };

            if disk_id_and_flags & 1 != 0 {
                // write
                let _ = memory.with_page(first_page, |page| {
                    storage
                        .write_storage(offset, &bytemuck::bytes_of(page)[first_page_offset..])
                        .unwrap_or(())
                });
                len -= first_page_tail_len;
                offset += first_page_tail_len;
                paddr += first_page_tail_len;

                while len >= size_of_as_u64::<Page>() {
                    let Ok(page) = (paddr >> 12).try_into() else {
                        return;
                    };
                    let _ = memory.with_page(page, |page| {
                        storage
                            .write_storage(offset, bytemuck::bytes_of(page))
                            .unwrap_or(())
                    });
                    len -= size_of_as_u64::<Page>();
                    offset += size_of_as_u64::<Page>();
                    paddr += size_of_as_u64::<Page>();
                }

                if len > 0 {
                    let _ = memory.with_page(first_page, |page| {
                        storage
                            .write_storage(
                                offset,
                                &bytemuck::bytes_of(page)[..(len.get() as usize)],
                            )
                            .unwrap_or(())
                    });
                }
            } else {
                let _ = memory.with_page_mut(first_page, |page| {
                    storage
                        .read_storage(
                            offset,
                            &mut bytemuck::bytes_of_mut(page)[first_page_offset..],
                        )
                        .unwrap_or(())
                });
                len -= first_page_tail_len;
                offset += first_page_tail_len;
                paddr += first_page_tail_len;

                while len >= size_of_as_u64::<Page>() {
                    let Ok(page) = (paddr >> 12).try_into() else {
                        return;
                    };
                    let _ = memory.with_page_mut(page, |page| {
                        storage
                            .read_storage(offset, bytemuck::bytes_of_mut(page))
                            .unwrap_or(())
                    });
                    len -= size_of_as_u64::<Page>();
                    offset += size_of_as_u64::<Page>();
                    paddr += size_of_as_u64::<Page>();
                }

                if len > 0 {
                    let _ = memory.with_page_mut(first_page, |page| {
                        storage
                            .read_storage(
                                offset,
                                &mut bytemuck::bytes_of_mut(page)[..(len.get() as usize)],
                            )
                            .unwrap_or(())
                    });
                }
            }
        }
    }
}
