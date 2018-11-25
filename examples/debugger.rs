extern crate melon;
extern crate rand;

use melon::typedef::*;
use melon::{Debugger, ProgramBuilder, System, VM};
use rand::{distributions::Standard, thread_rng, Rng};

const LIMIT: usize = 1000;

struct MyPerfectSystem {
    counter: usize,
}

impl MyPerfectSystem {
    pub fn new() -> MyPerfectSystem {
        MyPerfectSystem { counter: 0 }
    }
}

impl System for MyPerfectSystem {
    const ID: &'static str = "__WORMHOLE__";

    const MEM_PAGES: u8 = 8;

    fn prepare(&mut self, _: &mut VM) -> Result<()> {
        self.counter = 0;

        Ok(())
    }

    fn post_cycle(&mut self, _: &mut VM) -> Result<()> {
        self.counter += 1;

        Ok(())
    }
}

fn main() {
    let mut rng = thread_rng();

    let mut sys = MyPerfectSystem::new();

    let program = ProgramBuilder::new(MyPerfectSystem::ID)
        .instructions(rng.sample_iter(&Standard).take(LIMIT).collect())
        .gen();

    let exit_code = Debugger::default()
        .exec(&program, &mut sys)
        .unwrap_or_else(|e| {
            eprintln!("Error: {}", e);
            1
        });

    std::process::exit(i32::from(exit_code));
}
