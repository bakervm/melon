use crate::program::Program;
use crate::system::System;
use crate::typedef::*;
use crate::vm::VM;
use bytesize::ByteSize;
use colored::*;
use rustyline::Editor;
use std::{thread, time::Duration};

#[derive(Default)]
/// A simple interactive debugger for melon systems
pub struct Debugger {
    vm: VM,
}

impl Debugger {
    /// Executes the program inside a debugging environment with the original system context in mind
    pub fn exec<T: System>(&mut self, program: &Program, system: &mut T) -> Result<u8> {
        let mut debugger_system = DebuggerSystem::new(system);

        self.vm.exec(program, &mut debugger_system)
    }
}

enum RunMode {
    Run { delay: u64 },
    Step,
    Normal,
    Forward { cycle: usize },
}

struct DebuggerSystem<'a, T: System> {
    mode: RunMode,
    editor: Editor<()>,
    sub: &'a mut T,
    cycle_count: usize,
}

impl<'a, T: System> DebuggerSystem<'a, T> {
    pub fn new(sub: &mut T) -> DebuggerSystem<'_, T> {
        DebuggerSystem {
            mode: RunMode::Normal,
            editor: Editor::<()>::new(),
            sub: sub,
            cycle_count: 0,
        }
    }

    fn reset_mode(&mut self) {
        self.mode = RunMode::Normal;
    }
}

impl<'a, T: System> System for DebuggerSystem<'a, T> {
    const ID: &'static str = T::ID;

    const MEM_PAGES: u8 = T::MEM_PAGES;

    fn prepare(&mut self, vm: &mut VM) -> Result<()> {
        self.sub.prepare(vm)?;

        println!();

        let mem_line = format!("VM memory: {}", ByteSize(vm.mem.len() as u64));
        println!("{}", mem_line.cyan());

        let prog_line = format!(
            "Program memory: {}",
            ByteSize((vm.program.len() * 4) as u64)
        );
        println!("{}", prog_line.cyan());
        println!();

        Ok(())
    }

    fn pre_cycle(&mut self, vm: &mut VM) -> Result<()> {
        self.sub.pre_cycle(vm)?;

        let next_instruction = vm.current_instruction()?;
        let prompt = format!(
            "[#{}] {} > ",
            format!("{:04X}", vm.pc).red(),
            format!("{:?}", next_instruction).green()
        );

        loop {
            match self.mode {
                RunMode::Run { delay } => {
                    println!("{}", prompt);
                    thread::sleep(Duration::from_millis(delay));
                    break;
                }
                RunMode::Forward { cycle } => {
                    if cycle > 0 {
                        self.mode = RunMode::Forward { cycle: cycle - 1 };
                        break;
                    }

                    println!(
                        "Forwarded {} cycles to address #{}",
                        cycle,
                        format!("{:04X}", vm.pc).red()
                    );

                    self.reset_mode();
                }
                _ => {}
            }

            let readline = self.editor.readline(&prompt);

            let input = match readline {
                Ok(line) => line,
                Err(_) => {
                    vm.return_value = 1;
                    vm.halt();
                    break;
                }
            };

            self.editor.add_history_entry(input.trim());

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
                    vm.return_value = 0;
                    vm.halt();
                    break;
                }
                "run" | "r" => {
                    self.mode = RunMode::Run { delay: 0 };
                    println!("Running...");
                    println!();
                }
                "forward" | "f" => {
                    let readline = self.editor.readline("Forward N cycles: ")?;

                    if readline.is_empty() {
                        continue;
                    }

                    self.mode = RunMode::Forward {
                        cycle: readline.parse()?,
                    };
                }
                "rund" => {
                    self.mode = RunMode::Run { delay: 500 };
                    println!("Running with delayed steps...");
                    println!();
                }
                "step" | "s" => {
                    if let RunMode::Step = self.mode {
                        self.reset_mode();
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
                    println!("Stack {:X?}", &vm.mem[sp..max])
                }
                "pi" => {
                    println!("Dumping program memory");
                    println!();
                    let program = vm.program.clone();
                    for (pc, instruction) in program.into_iter().enumerate() {
                        let prompt = format!(
                            "[{}] {}",
                            format!("{:04X}", pc).red(),
                            format!("{:?}", instruction).green()
                        );
                        println!("{}", prompt)
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

        self.cycle_count += 1;

        Ok(())
    }

    fn finish(&mut self, vm: &mut VM) -> Result<()> {
        self.sub.finish(vm)?;

        self.reset_mode();

        Ok(())
    }

    fn system_call(&mut self, vm: &mut VM, signal: u16) -> Result<()> {
        self.sub.system_call(vm, signal)?;

        Ok(())
    }
}
