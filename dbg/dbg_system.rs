use melon::{typedef::*, System, VM};
use std::{io::{self, Write},
          thread,
          time::Duration};

#[derive(Default)]
pub struct DbgSystem {
    run: bool,
    step: bool,
    delay: u64,
}

impl System for DbgSystem {
    const ID: &'static str = "__DEBUG__";

    const MEM_PAGES: u8 = 0;

    fn prepare(&mut self, vm: &mut VM) -> Result<()> {
        println!("VM memory: {} bytes", vm.mem.len());
        println!("Program memory: {} bytes", vm.program().len() * 4);
        println!();

        Ok(())
    }

    fn pre_cycle(&mut self, vm: &mut VM) -> Result<()> {
        let next_instruction = vm.current_instruction()?;

        loop {
            let mut input = String::new();
            print!("[{}] {:?} > ", vm.pc(), next_instruction);
            io::stdout().flush()?;

            if self.run {
                println!();
                thread::sleep(Duration::from_millis(self.delay));
                break;
            }

            io::stdin().read_line(&mut input)?;

            match input.trim() {
                "help" | "h" => {
                    println!("Commands");
                    println!();
                    println!("help\t- prints this message");
                    println!("next\t- processes the next instruction");
                    println!("exit\t- exists the debugger");
                    println!("run\t- runs the program");
                    println!("rund\t- run the program with a delay after each instruction");
                    println!("step\t- toggle stepmode");
                    println!("ps\t- print the stack");
                    println!("pi\t- prints the current program with all its instructions");
                }
                "next" | "n" => break,
                "exit" | "q" => {
                    vm.return_value = 1;
                    vm.halt();
                    break;
                }
                "run" | "r" => {
                    self.run = true;
                    println!("Running...");
                    println!();
                }
                "rund" => {
                    self.run = true;
                    self.delay = 500;
                    println!("Running with delayed steps...");
                    println!();
                }
                "step" | "s" => {
                    if self.step {
                        self.step = false;
                        println!("Stepmode OFF");
                        println!();
                    } else {
                        self.step = true;
                        println!("Stepmode ON");
                        println!();
                    }
                }
                "ps" => {
                    let sp = vm.sp() as usize;
                    let max = vm.mem.len() - 1;
                    println!("Stack {:?}", &vm.mem[sp..max])
                }
                "pi" => {
                    println!("Dumping program memory");
                    println!();
                    let program = vm.program();
                    for (pc, instruction) in program.into_iter().enumerate() {
                        println!("[{}] {:?}", pc, instruction)
                    }
                }
                other if other.is_empty() => {
                    if self.step {
                        break;
                    }
                }
                other => eprintln!(
                    "unknown command {:?}. Type \"help\" to show the list of commands",
                    other
                ),
            }
        }

        Ok(())
    }
}
