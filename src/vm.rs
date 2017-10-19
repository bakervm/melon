use typedef::*;
use instruction::Instruction;
use program::Program;
use errors::*;
use shell::Shell;

const DEFAULT_MEM_SIZE: usize = 1024 * 1024 * 1014;

#[derive(Serialize, Deserialize, Default)]
pub struct VM {
    pc: usize,
    program: Vec<Instruction>,
    sp: usize,
    mem: Vec<Value>,
    return_value: u8,
    halted: bool,
}

impl VM {
    /// Executes the given program and returns it's exit status
    pub fn exec<T: Shell>(&mut self, program: Program, shell: &mut T) -> Result<u8> {
        ensure!(program.shell_id == T::ID, "Wrong shell ID");

        ensure!(
            program.core_version == env!("CARGO_PKG_VERSION"),
            "Wrong core version"
        );

        self.reset();

        shell.prepare(self)?;

        while (self.pc < self.program.len()) && !self.halted {
            self.do_cycle(shell)?;

            shell.process(self)?;
        }

        shell.finish(self)?;

        Ok(self.return_value)
    }

    /// Resets the VM to its default state
    fn reset(&mut self) {
        *self = Default::default();

        self.mem = vec![0; DEFAULT_MEM_SIZE];
        self.sp = DEFAULT_MEM_SIZE - 1;
    }

    /// Advances the program counter
    fn advance_pc(&mut self) {
        self.pc += 1;
    }

    fn do_cycle<T: Shell>(&mut self, shell: &mut T) -> Result<()> {
        let current_instruction = self.current_instruction()?;

        match current_instruction {
            Instruction::Flush => shell.flush(self)?,
            _ => unimplemented!(),
        }

        self.advance_pc();

        Ok(())
    }

    fn current_instruction(&mut self) -> Result<Instruction> {
        if let Some(current_instruction) = self.program.get(self.pc) {
            Ok(current_instruction.clone())
        } else {
            bail!("could no find instruction at {}", self.pc);
        }
    }
}
