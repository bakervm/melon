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
    cmp_res: Int,
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
        self.program = program.instructions.clone();

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
            Instruction::Int(signal) => shell.int(self, signal)?,
            Instruction::PushConstU8(value) => self.push_const_u8(value),
            Instruction::PushConstU16(value) => self.push_const_u16(value),
            Instruction::PushConstI8(value) => self.push_const_i8(value),
            Instruction::PushConstI16(value) => self.push_const_i16(value),
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
    fn read_u8(&mut self, addr: Address) -> SmallUInt {
        self.mem[addr as usize]
    }

    /// Writes the given small uint to the given address
    fn write_u8(&mut self, addr: Address, value: SmallUInt) {
        self.mem[addr as usize] = value;
    }

    /// Returns the uint at the given address
    fn read_u16(&mut self, addr: Address) -> UInt {
        let inner_addr_start = addr as usize;

        let value = <Endianess as ByteOrder>::read_u16(&mut self.mem[inner_addr_start..]);

        value
    }

    /// Writes the given uint to the given address
    fn write_u16(&mut self, addr: Address, value: UInt) {
        let inner_addr_start = addr as usize;

        <Endianess as ByteOrder>::write_u16(&mut self.mem[inner_addr_start..], value);
    }

    /// Helper method for popping a SmallUInt value off the stack
    fn pop_u8(&mut self) -> SmallUInt {
        let addr = self.sp;

        let value = self.read_u8(addr);

        self.sp += 1;

        value
    }

    /// Helper method for popping a UInt value off the stack
    fn pop_u16(&mut self) -> UInt {
        let addr = self.sp;

        let value = self.read_u16(addr);

        self.sp += 2;

        value
    }

    /// Helper method for popping a SmallInt value off the stack
    fn pop_i8(&mut self) -> SmallInt {
        let addr = self.sp;

        let value = self.read_u8(addr);

        self.sp += 1;

        value as SmallInt
    }

    /// Helper method for popping a Int value off the stack
    fn pop_i16(&mut self) -> Int {
        let addr = self.sp;

        let value = self.read_u16(addr);

        self.sp += 2;

        value as Int
    }

    // ####################
    // INSTRUCTION HANDLERS
    // ####################

    /// Handler for `Instruction::PushConstU8(SmallUInt)`
    fn push_const_u8(&mut self, value: SmallUInt) {
        self.sp -= 1;

        let addr = self.sp;

        self.write_u8(addr, value);
    }

    /// Handler for `Instruction::PushConstU16(UInt)`
    fn push_const_u16(&mut self, value: UInt) {
        self.sp -= 2;

        let addr = self.sp;

        self.write_u16(addr, value);
    }

    /// Handler for `Instruction::PushConstI8(SmallInt)`
    fn push_const_i8(&mut self, value: SmallInt) {
        self.sp -= 1;

        let addr = self.sp;

        self.write_u8(addr, value as SmallUInt);
    }

    /// Handler for `Instruction::PushConstI16(Int)`
    fn push_const_i16(&mut self, value: Int) {
        self.sp -= 2;

        let addr = self.sp;

        self.write_u16(addr, value as UInt);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{self, Rng};

    mod helper {
        use program::Program;
        use instruction::Instruction;
        use shell::Shell;

        #[derive(Default)]
        pub struct BogusShell {
            data: [u8; 8],
        }

        impl Shell for BogusShell {
            const ID: &'static str = "__BOGUS_SHELL__";
        }

        pub fn generate_shell() -> BogusShell {
            Default::default()
        }

        pub fn generate_program() -> Program {
            Program {
                core_version: env!("CARGO_PKG_VERSION").to_owned(),
                shell_id: "__BOGUS_SHELL__".to_owned(),
                instructions: generate_instructions(),
                mem_size: None,
            }
        }

        pub fn generate_instructions() -> Vec<Instruction> {
            vec![
                Instruction::PushConstU8(0xFF),
                Instruction::PushConstU16(0xFFFF),
                Instruction::PushConstI8(-120),
                Instruction::PushConstI16(-32000),
                Instruction::Int(123),
            ]
        }
    }

    #[test]
    fn byteorder_check() {
        let mut rng = rand::thread_rng();

        for _ in 0..3000 {
            let mut max = rng.gen_range(10, 300);

            let mut test_data: Vec<u8> = (0..max).map(|_| rng.gen()).collect();

            let addr_front_byte: u16 = rng.gen_range(0, max - 2);
            let addr_back_byte: u16 = addr_front_byte + 1;

            let value: u16 = rng.gen();

            let front_byte: u8 = ((value >> 8) & 0xFF) as u8;
            let back_byte: u8 = (value & 0xFF) as u8;

            let inner_addr_start = addr_front_byte as usize;

            <Endianess as ByteOrder>::write_u16(&mut test_data[inner_addr_start..], value);

            let mut asserted_vec = test_data.clone();
            asserted_vec[addr_front_byte as usize] = front_byte;
            asserted_vec[addr_back_byte as usize] = back_byte;

            assert_eq!(test_data, asserted_vec);
        }
    }

    #[test]
    fn stack_u8() {
        let mut vm = VM::default();
        vm.reset(&helper::generate_program()).unwrap();

        let mut rng = rand::thread_rng();

        for _ in 0..3000 {
            let test_value = rng.gen();

            vm.push_const_u8(test_value);
            assert_eq!(vm.pop_u8(), test_value);
        }
    }

    #[test]
    fn stack_i8() {
        let mut vm = VM::default();
        vm.reset(&helper::generate_program()).unwrap();

        let mut rng = rand::thread_rng();

        for _ in 0..3000 {
            let test_value = rng.gen();

            vm.push_const_i8(test_value);
            assert_eq!(vm.pop_i8(), test_value);
        }
    }

    #[test]
    fn stack_u16() {
        let mut vm = VM::default();
        vm.reset(&helper::generate_program()).unwrap();

        let mut rng = rand::thread_rng();

        for _ in 0..3000 {
            let test_value = rng.gen();

            vm.push_const_u16(test_value);
            assert_eq!(vm.pop_u16(), test_value);
        }
    }

    #[test]
    fn stack_i16() {
        let mut vm = VM::default();
        vm.reset(&helper::generate_program()).unwrap();

        let mut rng = rand::thread_rng();

        for _ in 0..3000 {
            let test_value = rng.gen();

            vm.push_const_i16(test_value);
            assert_eq!(vm.pop_i16(), test_value);
        }
    }

    #[test]
    fn bogus_execution() {
        let mut shell = helper::generate_shell();
        let program = helper::generate_program();

        let mut vm = VM::default();
        vm.exec(program, &mut shell).unwrap();
    }
}
