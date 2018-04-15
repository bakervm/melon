#[macro_use]
extern crate structopt;
extern crate melon;

mod dbg_system;

use dbg_system::DbgSystem;
use melon::typedef::*;
use melon::Program;
use melon::VM;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(StructOpt)]
struct Opt {
    #[structopt(parse(from_os_str))]
    file: PathBuf,
}

fn main() {
    match run() {
        Ok(_) => {}
        Err(e) => {
            eprintln!("{}", e);
            ::std::process::exit(1);
        }
    }
}

fn run() -> Result<()> {
    let opts = Opt::from_args();

    let mut program = Program::from_file(opts.file)?;
    program.system_id = "__DEBUG__".into();

    let mut system = DbgSystem::default();

    VM::default().exec(&program, &mut system)?;

    Ok(())
}
