// Copyright (c) 2017 Julian Laubstein
//
// GNU GENERAL PUBLIC LICENSE
//    Version 3, 29 June 2007
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use typedef::*;
use instruction::Instruction;
use program::Program;
use shell::Shell;
use byteorder::{BigEndian, ByteOrder};

type Endianess = BigEndian;

/// A constant used to calulate the actually used memory of the VM
pub const KILOBYTE: Address = 1024;
/// A constant defining the default memory size of the VM
const DEFAULT_MEM_SIZE_KILOBYTE: Address = 32;
/// A constant defining the maximum memory size of the VM
const MAX_MEM_SIZE_KILOBYTE: Address = 64;

/// The state of the VM
#[derive(Serialize, Deserialize, Default)]
pub struct VM {
    /// The program counter
    pc: Address,
    /// The program data
    program: Vec<Instruction>,
    /// The stack pointer
    sp: Address,
    /// The base pointer
    bp: Address,
    /// The memory allocated and used by the VM
    pub mem: Vec<SmallUInt>,
    /// The return value of the VM
    pub return_value: SmallUInt,
    halted: bool,
}

impl VM {
    /// Executes the given program using the given shell and returns the program's exit status
    pub fn exec<T: Shell>(&mut self, program: Program, shell: &mut T) -> Result<SmallUInt> {
        ensure!(program.shell_id == T::ID, "wrong shell ID");

        ensure!(
            program.core_version == env!("CARGO_PKG_VERSION"),
            "wrong core version"
        );

        if let Some(mem_size) = program.mem_size {
            ensure!(mem_size < MAX_MEM_SIZE_KILOBYTE, "requested memory too big");

            ensure!(mem_size > 0, "requested memory too small");
        }

        self.reset(&program)?;

        shell.prepare(self)?;

        while (self.pc < self.program.len() as Address) && !self.halted {
            self.do_cycle(shell)?;

            shell.process(self)?;
        }

        shell.finish(self)?;

        Ok(self.return_value)
    }

    /// Resets the VM to its default state
    fn reset(&mut self, program: &Program) -> Result<()> {
        *self = Default::default();

        let mem_size = program.mem_size.unwrap_or(DEFAULT_MEM_SIZE_KILOBYTE) * KILOBYTE;

        ensure!(
            self.program.len() < mem_size as usize,
            "program memory too big"
        );

        self.mem = vec![0; mem_size as usize];
        self.sp = (mem_size - 1) as Address;

        Ok(())
    }

    /// Advances the program counter
    fn advance_pc(&mut self) {
        self.pc += 1;
    }

    /// Returns the instruction at the current pc
    fn current_instruction(&mut self) -> Result<Instruction> {
        if let Some(current_instruction) = self.program.get(self.pc as usize) {
            Ok(current_instruction.clone())
        } else {
            bail!("could no find instruction at {:04X}", self.pc);
        }
    }

    /// Consume and execute a single instruction
    fn handle_instruction<T: Shell>(
        &mut self,
        instruction: Instruction,
        shell: &mut T,
    ) -> Result<()> {
        match instruction {
            Instruction::Int(addr) => shell.int(self, addr)?,
            _ => bail!("instruction {:?} is not yet implemented", instruction),
        }

        Ok(())
    }

    /// Runs one execution cycle
    fn do_cycle<T: Shell>(&mut self, shell: &mut T) -> Result<()> {
        let current_instruction = self.current_instruction()?;

        self.advance_pc();

        self.handle_instruction(current_instruction, shell)?;

        Ok(())
    }

    /// Returns the small uint at the given address
    fn read_small_uint(&mut self, addr: Address) -> SmallUInt {
        self.mem[addr as usize]
    }

    /// Writes the given small uint to the given address
    fn write_small_uint(&mut self, addr: Address, value: SmallUInt) {
        self.mem[addr as usize] = value;
    }

    /// Returns the uint at the given address
    fn read_uint(&mut self, addr: Address) -> UInt {
        let inner_addr_start = addr as usize;

        let value = <Endianess as ByteOrder>::read_u16(&mut self.mem[inner_addr_start..]);

        value
    }

    /// Writes the given uint to the given address
    fn write_uint(&mut self, addr: Address, value: UInt) {
        let inner_addr_start = addr as usize;

        <Endianess as ByteOrder>::write_u16(&mut self.mem[inner_addr_start..], value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byteorder_check() {
        let mut test_data = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

        let addr = 3;
        let value: u16 = 0x2233;

        let inner_addr_start = addr as usize;

        <Endianess as ByteOrder>::write_u16(&mut test_data[inner_addr_start..], value);

        assert_eq!(test_data, vec![0, 1, 2, 0x22, 0x33, 5, 6, 7, 8, 9]);
    }
}
