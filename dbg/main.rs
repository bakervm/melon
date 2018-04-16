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
    #[structopt(parse(from_os_str), help = "the rom file to debug")]
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
    // We *force* compatablilty to the DbgSystem
    program.system_id = "__DEBUG__".into();

    println!("Starting melonDbg");
    println!("=================");
    println!();

    loop {
        let ret = VM::default().exec(&program, &mut DbgSystem::default());

        match ret {
            Ok(val) => {
                if val > 0 {
                    break;
                }
            }
            Err(err) => eprintln!("{}", err),
        }

        println!("Restarting...");
        println!();
    }

    Ok(())
}
