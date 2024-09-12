use std::{borrow::Cow, env::Args, io, path::PathBuf, process::ExitCode};

use clever_emu_mem::cache::CacheFetch;
use clever_emu_primitives::primitive::{LeU32, LeU64};

use emu_state_builder::EmuStateBuilder;

use helpers::SplitOnceOwned;

mod emu_state_builder;
mod helpers;
mod serial;

fn real_main(mut args: Args) -> io::Result<()> {
    let mut state = EmuStateBuilder::default();

    while let Some(arg) = args.next() {
        let (arg, explicit) = arg
            .split_once("=")
            .map(|(a, b)| (a, Some(b)))
            .unwrap_or((&arg, None));

        match arg {
            "--firmware" => state.firmware(PathBuf::from(
                require_arg(Some("--firmware"), &mut args, explicit)?.into_owned(),
            )),
            "--attach-storage" => state.attach_storage(&*require_arg(
                Some("--attach-storage"),
                &mut args,
                explicit,
            )?)?,
            "--attach-display" => {
                if explicit.is_some() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "--attach-display does not take an argument",
                    ));
                }

                state.attach_display()?;
            }
            "--attach-serial" => {
                state.attach_serial(&*require_arg(Some("--attach-serial"), &mut args, explicit)?)?
            }
            x => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Unrecognized argument {x}"),
                ))
            }
        }
    }

    let mut exec = state.create_executor()?;
    exec.init();
    exec.global_memory()
        .inner()
        .with_page(LeU32::new(15), |pg| {
            eprintln!("{:x?}", &bytemuck::bytes_of(pg)[0xF00..]);
        })
        .unwrap();
    let (line, _) = exec
        .global_memory()
        .inner()
        .read_line(LeU64::new(0xFF00))
        .unwrap();
    eprintln!("{:x?}", line);

    let (line, _) = exec.global_memory().read_line(LeU64::new(0xFF00)).unwrap();
    eprintln!("{:x?}", line);
    let _ = exec.run();

    eprintln!("Reset");

    Ok(())
}

fn require_arg<'a, I: Iterator<Item = String>>(
    flag: Option<&str>,
    args: &mut I,
    explicit: Option<&'a str>,
) -> io::Result<Cow<'a, str>> {
    explicit
        .map(Cow::Borrowed)
        .or_else(|| args.next().map(Cow::Owned))
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                if let Some(flag) = flag {
                    format!("{} requires an argument", flag)
                } else {
                    format!("Expected an argument")
                },
            )
        })
}

fn main() -> ExitCode {
    let mut args = std::env::args();

    let prg_name = args.next().unwrap_or_else(|| "clever-emu".to_string());

    match real_main(args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{prg_name}: {e}");
            ExitCode::FAILURE
        }
    }
}
