use melon::{typedef::*, System, VM};
use std::io::{self, Write};

#[derive(Default)]
pub struct DbgSystem {
    paused: bool,
}

impl System for DbgSystem {
    const ID: &'static str = "__DEBUG__";

    const MEM_PAGES: u8 = 0;

    fn pre_cycle(&mut self, vm: &mut VM) -> Result<()> {
        let mut input = String::new();

        let current_instruction = vm.current_instruction()?;

        print!("[{}] {:?} > ", vm.pc(), current_instruction);
        io::stdout().flush()?;
        io::stdin().read_line(&mut input)?;
        Ok(())
    }
}
