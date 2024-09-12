use std::{
    ffi::OsStr,
    fs,
    io::{self, Read},
    num::NonZero,
    path::{Path, PathBuf},
    sync::Arc,
};

#[cfg(feature = "aci")]
use clever_emu_aci::root::RootBridge;
use clever_emu_cpu::{
    cpu::{Cpu, CpuMemorySizes},
    executor::CpuExecutor,
};
use clever_emu_mem::{
    io::IoBus,
    phys::{Page, SysMemory},
};
use clever_emu_primitives::{
    nzlit,
    primitive::{LeU32, LeU64},
    size_of_as_u64,
};
#[cfg(feature = "iodma")]
use clever_emu_storage::interface::iodma::InterfaceIodma;
#[cfg(feature = "spi")]
use clever_emu_storage::interface::spi::SpiController;
use clever_emu_storage::store::{DirectStorage, StorageMode};
#[cfg(feature = "wgpu")]
use clever_emu_wgpu::device::WgpuDevice;

use crate::serial::SerialDevice;

#[derive(Default)]
pub struct EmuStateBuilder {
    #[cfg(feature = "aci")]
    root_bridge: RootBridge,
    #[cfg(feature = "iodma")]
    iodma_bus: InterfaceIodma,
    #[cfg(feature = "spi")]
    spi_controller: SpiController,
    cpu_memory_sizes: CpuMemorySizes,
    firmware_path: Option<PathBuf>,
    iobus: IoBus,
    num_cpus: Option<NonZero<usize>>,
}

impl EmuStateBuilder {
    pub const fn new() -> EmuStateBuilder {
        EmuStateBuilder {
            cpu_memory_sizes: CpuMemorySizes::new(),
            num_cpus: None,
            firmware_path: None,
            iobus: IoBus::new(),
            #[cfg(feature = "aci")]
            root_bridge: RootBridge::new(),
            #[cfg(feature = "iodma")]
            iodma_bus: InterfaceIodma::new(),
            #[cfg(feature = "spi")]
            spi_controller: SpiController::new(),
        }
    }

    pub fn firmware(&mut self, path: PathBuf) {
        self.firmware_path = Some(path);
    }

    pub fn attach_serial(&mut self, file: &str) -> io::Result<()> {
        let (mode, file) = file
            .split_once(":")
            .map(|(mode, file)| match mode {
                "readonly" => Ok((StorageMode::ReadOnly, file)),
                "readwrite" => Ok((StorageMode::ReadWrite, file)),
                mode => Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Invalid storage mode {mode}"),
                )),
            })
            .unwrap_or(Ok((StorageMode::ReadWrite, file)))?;

        let serial = if file == "-" {
            SerialDevice::open_tty()?
        } else {
            SerialDevice::open(Path::new(file), mode)?
        };

        self.iobus.attach_port(serial);
        Ok(())
    }

    /// Attaches a Display Device
    pub fn attach_display(&mut self) -> io::Result<()> {
        #[cfg(feature = "wgpu")]
        {
            self.root_bridge.attach(WgpuDevice::new());

            Ok(())
        }
        #[cfg(not(feature = "wgpu"))]
        {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "--attach-display requires feature wgpu to be enabled",
            ))
        }
    }

    pub fn attach_storage(&mut self, arg: &str) -> io::Result<()> {
        let (kind, target) = arg.split_once("=").ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "--attach-storage requires an argument of form kind=file or kind=mode:file",
            )
        })?;

        let (mode, file) = arg
            .split_once(":")
            .map(|(mode, file)| match mode {
                "readonly" => Ok((StorageMode::ReadOnly, file)),
                "readwrite" => Ok((StorageMode::ReadWrite, file)),
                mode => Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Invalid storage mode {mode}"),
                )),
            })
            .unwrap_or(Ok((StorageMode::ReadWrite, target)))?;

        let (explicit_format, file) = match file.split_once(":") {
            Some((fmt, file)) => (fmt, Path::new(file)),
            None => {
                let file = Path::new(file);
                match file.extension().and_then(OsStr::to_str){
                    Some("img" | "iso" | "ima") | None => ("raw", file),
                    Some("vhd") => ("vhd",file),
                    Some(ext) => return Err(io::Error::new(io::ErrorKind::InvalidInput, format!("Extension {ext} was not recognized (detected by extension: If the extension is wrong use the mode option")))
                }
            }
        };

        let storage = match explicit_format {
            "raw" => Box::new(DirectStorage::open(file, mode)?),
            #[cfg(feature = "vhd")]
            "vhd" => todo!("MS VHD Format"),
            #[cfg(not(feature = "vhd"))]
            "vhd" => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Unrecognized format vhd (Using the vhd format requires the vhd feature)"),
            ))?,
            fmt => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Unrecognized format {fmt}"),
            ))?,
        };

        match kind {
            #[cfg(feature = "iodma")]
            "iodma" => self.iodma_bus.attach_dyn(storage),
            kind => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Invalid I/O Device kind {kind}"),
            ))?,
        }
        Ok(())
    }

    pub fn create_executor(mut self) -> io::Result<CpuExecutor> {
        let sysmem = Arc::new(SysMemory::new(
            (self.cpu_memory_sizes.sys_mem_size / size_of::<Page>()) as u32,
        ));

        let mut firmware = fs::File::open(
            self.firmware_path
                .as_deref()
                .unwrap_or_else(|| Path::new("bios")),
        )?;

        for i in 0..16 {
            sysmem
                .with_page_mut(LeU32::new(i), |page| {
                    firmware.read_exact(bytemuck::bytes_of_mut(page))
                })
                .map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!(
                            "Invalid value for {} - must be at least 64k to load the bios",
                            self.cpu_memory_sizes.sys_mem_size
                        ),
                    )
                })??;
        }

        #[cfg(feature = "iodma")]
        {
            self.iodma_bus.set_memory_bus(Arc::clone(&sysmem));
            self.iobus.attach_port(self.iodma_bus);
        }

        #[cfg(feature = "aci")]
        {
            let root_bridge = Arc::new(self.root_bridge);

            self.iobus
                .attach_shared_port(Arc::<RootBridge>::clone(&root_bridge));
            self.iobus.attach_shared_mmio(root_bridge);
        }

        Ok(CpuExecutor::new(
            self.num_cpus
                .or_else(|| std::thread::available_parallelism().ok())
                .unwrap_or(nzlit!(1)),
            self.cpu_memory_sizes,
            sysmem,
            self.iobus,
        ))
    }
}
