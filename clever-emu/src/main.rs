mod emu_state_builder;

fn main() {
    let mut args = std::env::args();

    let prg_name = args.next().unwrap_or_else(|| "clever-emu".to_string());

    while let Some(arg) = args.next() {}
}
