//! A sample debugger implementation for testing the debugger itself.

use melon::{Instruction, Debugger, System, ProgramBuilder};

pub struct DumbSystem;

impl System for DumbSystem {
    const ID: &'static str = "org.test.dumb";

    const MEM_PAGES: u8 = 0;
}

fn main() {
    let dumb_program = ProgramBuilder::new("org.test.dumb")
        .instructions(vec![Instruction::SysCall(0)])
        .gen();

    Debugger::default()
        .exec(&dumb_program, &mut DumbSystem)
        .expect("executing the debugger didn't work");
}
