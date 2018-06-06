use program::Program;
use rustyline::Editor;
use std::{thread, time::Duration};
use system::System;
use typedef::*;
use vm::VM;

#[derive(Default)]
/// A simple interactive debugger for melon systems
pub struct Debugger {
    vm: VM,
}

impl Debugger {
    /// Executes the program inside a debugging environment with the original system context in mind
    pub fn exec<T: System>(&mut self, program: &Program, system: &mut T) -> Result<()> {
        let mut debugger_system = DebuggerSystem::new(system);

        loop {
            let ret = self.vm.exec(program, &mut debugger_system);

            match ret {
                Ok(val) if val > 0 => break,
                Ok(..) => {}
                Err(err) => match err.downcast()? {
                    error @ VMError::WrongTargetVersion { .. } => {
                        eprintln!("{}", error);
                        break;
                    }
                    other => eprintln!("{}", other),
                },
            }
        }

        Ok(())
    }
}

enum RunMode {
    Run { delay: u64 },
    Step,
    Normal,
}

struct DebuggerSystem<'a, T: 'a + System> {
    mode: RunMode,
    editor: Editor<()>,
    sub: &'a mut T,
}

impl<'a, T: System> DebuggerSystem<'a, T> {
    pub fn new(sub: &mut T) -> DebuggerSystem<T> {
        DebuggerSystem {
            mode: RunMode::Normal,
            editor: Default::default(),
            sub: sub,
        }
    }
}

impl<'a, T: System> System for DebuggerSystem<'a, T> {
    const ID: &'static str = T::ID;

    const MEM_PAGES: u8 = T::MEM_PAGES;

    fn prepare(&mut self, vm: &mut VM) -> Result<()> {
        self.sub.prepare(vm)?;

        println!();
        println!("VM memory: {} bytes", vm.mem.len());
        println!("Program memory: {} bytes", vm.program.len() * 4);
        println!();

        Ok(())
    }

    fn pre_cycle(&mut self, vm: &mut VM) -> Result<()> {
        self.sub.pre_cycle(vm)?;

        let next_instruction = vm.current_instruction()?;
        let prompt = format!("[{}] {:?} > ", vm.pc, next_instruction);

        loop {
            if let RunMode::Run { delay } = self.mode {
                println!("{}", prompt);
                thread::sleep(Duration::from_millis(delay));
                break;
            }

            let readline = self.editor.readline(&prompt);

            let input = match readline {
                Ok(line) => line,
                Err(_) => {
                    vm.return_value = 100;
                    vm.halt();
                    break;
                }
            };

            self.editor.add_history_entry(&input.trim());

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
                    self.mode = RunMode::Run { delay: 0 };
                    println!("Running...");
                    println!();
                }
                "rund" => {
                    self.mode = RunMode::Run { delay: 500 };
                    println!("Running with delayed steps...");
                    println!();
                }
                "step" | "s" => {
                    if let RunMode::Step = self.mode {
                        self.mode = RunMode::Normal;
                        println!("Stepmode OFF");
                        println!();
                    } else {
                        self.mode = RunMode::Step;
                        println!("Stepmode ON");
                        println!();
                    }
                }
                "ps" => {
                    let sp = vm.sp as usize;
                    let max = vm.mem.len() - 1;
                    println!("Stack {:?}", &vm.mem[sp..max])
                }
                "pi" => {
                    println!("Dumping program memory");
                    println!();
                    let program = vm.program.clone();
                    for (pc, instruction) in program.into_iter().enumerate() {
                        println!("[{}] {:?}", pc, instruction)
                    }
                }
                other if other.is_empty() => {
                    if let RunMode::Step = self.mode {
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

    fn post_cycle(&mut self, vm: &mut VM) -> Result<()> {
        self.sub.post_cycle(vm)?;

        Ok(())
    }

    fn finish(&mut self, vm: &mut VM) -> Result<()> {
        self.sub.finish(vm)?;

        self.mode = RunMode::Normal;

        Ok(())
    }

    fn system_call(&mut self, vm: &mut VM, signal: u16) -> Result<()> {
        self.sub.system_call(vm, signal)?;

        Ok(())
    }
}
