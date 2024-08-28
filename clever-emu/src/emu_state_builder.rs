#[cfg(feature = "aci")]
use clever_emu_aci::root::RootBridge;
use clever_emu_mem::io::IoBus;

pub struct EmuStateBuilder {
    #[cfg(feature = "aci")]
    root_bridge: Option<RootBridge>,
    iobus: IoBus,
}
