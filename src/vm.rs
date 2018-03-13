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
use instruction::{Instruction, IntegerType, Register};
use program::Program;
use shell::Shell;
use byteorder::{BigEndian, ByteOrder};

type Endianess = BigEndian;

/// A constant used to calulate the actually used memory of the VM
pub const MEM_PAGE: Address = 1024;
/// A constant defining the default memory size of the VM
const DEFAULT_MEM_PAGE_COUNT: Address = 32;
/// A constant defining the maximum memory size of the VM
const MAX_MEM_PAGE_COUNT: Address = 64;

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
    pub fn exec<T: Shell>(&mut self, program: &Program, shell: &mut T) -> Result<SmallUInt> {
        ensure!(program.shell_id == T::ID, "wrong shell ID");

        ensure!(
            program.core_version == env!("CARGO_PKG_VERSION"),
            "wrong core version"
        );

        if let Some(mem_size) = program.mem_size {
            ensure!(mem_size <= MAX_MEM_PAGE_COUNT, "requested memory too big");

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

        let mem_size = program.mem_size.unwrap_or(DEFAULT_MEM_PAGE_COUNT) * MEM_PAGE;

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
            bail!("could no find instruction at ${:04X}", self.pc);
        }
    }

    /// Consume and execute a single instruction
    fn handle_instruction<T: Shell>(
        &mut self,
        instruction: Instruction,
        shell: &mut T,
    ) -> Result<()> {
        match instruction {
            Instruction::Add(ty) => self.add(ty)?,
            Instruction::Sub(ty) => self.sub(ty)?,
            Instruction::Mul(ty) => self.mul(ty)?,
            Instruction::Div(ty) => self.div(ty)?,
            Instruction::Shr(ty) => self.shr(ty)?,
            Instruction::Shl(ty) => self.shl(ty)?,
            Instruction::And(ty) => self.and(ty)?,
            Instruction::Or(ty) => self.or(ty)?,
            Instruction::Xor(ty) => self.xor(ty)?,
            // Instruction::Neg(ty) => self.neg(ty)?,
            // Instruction::Not(ty) => self.not(ty)?,
            // Instruction::Cmp(ty) => self.cmp(ty)?,
            // Instruction::Inc(ty) => self.inc(ty)?,
            // Instruction::Dec(ty) => self.dec(ty)?,
            Instruction::PushConstU8(value) => self.push_const_u8(value)?,
            Instruction::PushConstU16(value) => self.push_const_u16(value)?,
            Instruction::PushConstI8(value) => self.push_const_i8(value)?,
            Instruction::PushConstI16(value) => self.push_const_i16(value)?,
            Instruction::LoadReg(reg) => self.load_reg(reg)?,
            Instruction::Load(ty, addr) => self.load(ty, addr)?,
            Instruction::Store(ty, addr) => self.store(ty, addr)?,
            // Instruction::Dup(ty) => self.dup(ty)?,
            // Instruction::Drop(ty) => self.drop(ty)?,
            Instruction::Int(0) => self.halt(),
            Instruction::Int(signal) => shell.int(self, signal)?,
            // Instruction::Call(addr) => self.call(addr),
            // Instruction::Ret => self.ret(),
            // Instruction::Jmp(int) => self.jmp(int),
            // Instruction::Jnz(int) => self.jnz(int),
            // Instruction::Jz(int) => self.jz(int),
            // Instruction::Jn(int) => self.jn(int),
            // Instruction::Jp(int) => self.jp(int),
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

    /// Stops execution and shuts down the VM
    pub fn halt(&mut self) {
        self.halted = true;
    }

    /// Helper function to ensure the validity of a memory address
    fn ensure_valid_mem_addr(&mut self, addr: Address) -> Result<()> {
        ensure!(
            addr < (self.mem.len() as Address),
            "memory address out of bounds"
        );

        Ok(())
    }

    /// Returns the small uint at the given address
    pub fn read_u8(&mut self, addr: Address) -> Result<SmallUInt> {
        self.ensure_valid_mem_addr(addr)?;

        Ok(self.mem[addr as usize])
    }

    /// Writes the given small uint to the given address
    pub fn write_u8(&mut self, addr: Address, value: SmallUInt) -> Result<()> {
        self.ensure_valid_mem_addr(addr)?;

        self.mem[addr as usize] = value;

        Ok(())
    }

    /// Returns the uint at the given address
    pub fn read_u16(&mut self, addr: Address) -> Result<UInt> {
        self.ensure_valid_mem_addr(addr + 1)?;

        let inner_addr_start = addr as usize;

        let value = <Endianess as ByteOrder>::read_u16(&self.mem[inner_addr_start..]);

        Ok(value)
    }

    /// Writes the given uint to the given address
    pub fn write_u16(&mut self, addr: Address, value: UInt) -> Result<()> {
        self.ensure_valid_mem_addr(addr + 1)?;

        let inner_addr_start = addr as usize;

        <Endianess as ByteOrder>::write_u16(&mut self.mem[inner_addr_start..], value);

        Ok(())
    }

    /// Helper method for popping a SmallUInt value off the stack
    pub fn pop_u8(&mut self) -> Result<SmallUInt> {
        let addr = self.sp;

        let value = self.read_u8(addr)?;

        self.sp += 1;

        Ok(value)
    }

    /// Helper method for popping a UInt value off the stack
    pub fn pop_u16(&mut self) -> Result<UInt> {
        let addr = self.sp;

        let value = self.read_u16(addr)?;

        self.sp += 2;

        Ok(value)
    }

    /// Helper method for popping a SmallInt value off the stack
    pub fn pop_i8(&mut self) -> Result<SmallInt> {
        let addr = self.sp;

        let value = self.read_u8(addr)?;

        self.sp += 1;

        Ok(value as SmallInt)
    }

    /// Helper method for popping a Int value off the stack
    pub fn pop_i16(&mut self) -> Result<Int> {
        let addr = self.sp;

        let value = self.read_u16(addr)?;

        self.sp += 2;

        Ok(value as Int)
    }

    /// Returns two u8 values as (left-hand-side, right-hand-side)
    pub fn pop_u8_lr(&mut self) -> Result<(SmallUInt, SmallUInt)> {
        let b = self.pop_u8()?;
        let a = self.pop_u8()?;

        Ok((a, b))
    }

    /// Returns two u16 values as (left-hand-side, right-hand-side)
    pub fn pop_u16_lr(&mut self) -> Result<(UInt, UInt)> {
        let b = self.pop_u16()?;
        let a = self.pop_u16()?;

        Ok((a, b))
    }

    /// Returns two i8 values as (left-hand-side, right-hand-side)
    pub fn pop_i8_lr(&mut self) -> Result<(SmallInt, SmallInt)> {
        let b = self.pop_i8()?;
        let a = self.pop_i8()?;

        Ok((a, b))
    }

    /// Returns two i16 values as (left-hand-side, right-hand-side)
    pub fn pop_i16_lr(&mut self) -> Result<(Int, Int)> {
        let b = self.pop_i16()?;
        let a = self.pop_i16()?;

        Ok((a, b))
    }

    // ####################
    // INSTRUCTION HANDLERS
    // ####################

    /// Handler for `Instruction::PushConstU8(SmallUInt)`
    pub fn push_const_u8(&mut self, value: SmallUInt) -> Result<()> {
        self.sp -= 1;

        let addr = self.sp;

        self.write_u8(addr, value)
    }

    /// Handler for `Instruction::PushConstU16(UInt)`
    pub fn push_const_u16(&mut self, value: UInt) -> Result<()> {
        self.sp -= 2;

        let addr = self.sp;

        self.write_u16(addr, value)
    }

    /// Handler for `Instruction::PushConstI8(SmallInt)`
    pub fn push_const_i8(&mut self, value: SmallInt) -> Result<()> {
        self.sp -= 1;

        let addr = self.sp;

        self.write_u8(addr, value as SmallUInt)
    }

    /// Handler for `Instruction::PushConstI16(Int)`
    pub fn push_const_i16(&mut self, value: Int) -> Result<()> {
        self.sp -= 2;

        let addr = self.sp;

        self.write_u16(addr, value as UInt)
    }

    /// Handler for `Instruction::LoadReg(Register)`
    pub fn load_reg(&mut self, reg: Register) -> Result<()> {
        let ptr = match reg {
            Register::StackPtr => self.sp,
            Register::BasePtr => self.bp,
        };

        self.push_const_u16(ptr)
    }

    /// Handler for `Instruction::Load(IntegerType, Address)`
    pub fn load(&mut self, ty: IntegerType, addr: Address) -> Result<()> {
        match ty {
            IntegerType::U8 | IntegerType::I8 => {
                let value = self.read_u8(addr)?;
                self.push_const_u8(value)?;
            }
            IntegerType::U16 | IntegerType::I16 => {
                let value = self.read_u16(addr)?;
                self.push_const_u16(value)?;
            }
        }

        Ok(())
    }

    /// Handler for `Instruction::Store(IntegerType, Address)`
    pub fn store(&mut self, ty: IntegerType, addr: Address) -> Result<()> {
        match ty {
            IntegerType::U8 | IntegerType::I8 => {
                let value = self.pop_u8()?;
                self.write_u8(addr, value)?;
            }
            IntegerType::U16 | IntegerType::I16 => {
                let value = self.pop_u16()?;
                self.write_u16(addr, value)?;
            }
        }

        Ok(())
    }

    /// Pops two values of the given type off the stack, *adds* them together and pushes the result
    /// back on the stack
    pub fn add(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a + b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a + b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a + b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a + b)
            }
        }
    }

    /// Pops two values of the given type off the stack, *subtracts* the second from the first and
    /// pushes the result back on the stack
    pub fn sub(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a - b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a - b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a - b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a - b)
            }
        }
    }

    /// Pops two values of the given type off the stack, *multiplies* them and pushes the result
    /// back on the stack
    pub fn mul(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a * b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a * b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a * b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a * b)
            }
        }
    }

    /// Pops two values of the given type off the stack, *divides* the first through the second and
    /// pushes the result back on the stack
    pub fn div(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a / b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a / b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a / b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a / b)
            }
        }
    }

    /// Pops two values of the given type off the stack, uses the second one to shift the bits
    /// of the first one to the *right* and pushes the result back onto the stack
    pub fn shr(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a >> b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a >> b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a >> b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a >> b)
            }
        }
    }

    /// Pops two values of the given type off the stack, uses the second one to shift the bits
    /// of the first one to the *left* and pushes the result back onto the stack
    pub fn shl(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a << b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a << b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a << b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a << b)
            }
        }
    }

    /// Pops two values of the given type off the stack, applies a *bitwise and* to both and
    /// pushes the result back onto the stack
    pub fn and(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a & b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a & b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a & b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a & b)
            }
        }
    }

    /// Pops two values of the given type off the stack, applies a *bitwise or* to both and
    /// pushes the result back onto the stack
    pub fn or(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a | b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a | b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a | b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a | b)
            }
        }
    }

    /// Pops two values of the given type off the stack, applies a *bitwise or* to both and
    /// pushes the result back onto the stack
    pub fn xor(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.push_const_u8(a ^ b)
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.push_const_u16(a ^ b)
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.push_const_i8(a ^ b)
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.push_const_i16(a ^ b)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{self, Rng};
    use instruction::{Instruction, IntegerType};

    mod helper {
        use program::Program;
        use instruction::{Instruction, IntegerType, Register};
        use shell::Shell;

        #[derive(Default)]
        pub struct BogusShell {
            _data: [u8; 8],
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
                shell_id: BogusShell::ID.to_owned(),
                instructions: generate_instructions(),
                mem_size: Some(63),
            }
        }

        pub fn generate_instructions() -> Vec<Instruction> {
            vec![
                Instruction::PushConstU8(0xFF),
                Instruction::PushConstU16(0xFFFF),
                Instruction::PushConstI8(-120),
                Instruction::PushConstI16(-32000),
                Instruction::LoadReg(Register::StackPtr),
                Instruction::LoadReg(Register::BasePtr),
                Instruction::Store(IntegerType::U8, 0xABCD),
                Instruction::Store(IntegerType::U16, 0xACBD),
                Instruction::Store(IntegerType::I8, 0xBACD),
                Instruction::Store(IntegerType::I16, 0xABDC),
                Instruction::Load(IntegerType::U8, 0xABCD),
                Instruction::Load(IntegerType::U16, 0xACBD),
                Instruction::Load(IntegerType::I8, 0xBACD),
                Instruction::Load(IntegerType::I16, 0xABDC),
                Instruction::Int(123),
            ]
        }
    }

    #[test]
    fn byteorder_check() {
        let mut rng = rand::thread_rng();

        for _ in 0..300 {
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

        for _ in 0..300 {
            let test_value = rng.gen();

            vm.push_const_u8(test_value).unwrap();
            assert_eq!(vm.pop_u8().unwrap(), test_value);
        }
    }

    #[test]
    fn stack_i8() {
        let mut vm = VM::default();
        vm.reset(&helper::generate_program()).unwrap();

        let mut rng = rand::thread_rng();

        for _ in 0..300 {
            let test_value = rng.gen();

            vm.push_const_i8(test_value).unwrap();
            assert_eq!(vm.pop_i8().unwrap(), test_value);
        }
    }

    #[test]
    fn stack_u16() {
        let mut vm = VM::default();
        vm.reset(&helper::generate_program()).unwrap();

        let mut rng = rand::thread_rng();

        for _ in 0..300 {
            let test_value = rng.gen();

            vm.push_const_u16(test_value).unwrap();
            assert_eq!(vm.pop_u16().unwrap(), test_value);
        }
    }

    #[test]
    fn stack_i16() {
        let mut vm = VM::default();
        vm.reset(&helper::generate_program()).unwrap();

        let mut rng = rand::thread_rng();

        for _ in 0..300 {
            let test_value = rng.gen();

            vm.push_const_i16(test_value).unwrap();
            assert_eq!(vm.pop_i16().unwrap(), test_value);
        }
    }

    #[test]
    fn simple_execution() {
        let mut shell = helper::generate_shell();
        let program = helper::generate_program();

        let mut vm = VM::default();
        vm.exec(&program, &mut shell).unwrap();
    }

    #[test]
    #[should_panic]
    fn vm_without_program() {
        let mut vm = VM::default();
        vm.pc = 20;

        vm.current_instruction().unwrap();
    }

    #[test]
    fn pc_out_of_bounds() {
        let mut shell = helper::generate_shell();
        let program = helper::generate_program();

        let mut vm = VM::default();
        vm.pc = (program.instructions.len() + 20) as Address;

        vm.exec(&program, &mut shell).unwrap();
    }

    #[test]
    fn int_exec() {
        for i in 0..300 {
            let mut shell = helper::generate_shell();
            let mut program = helper::generate_program();
            program.instructions = vec![Instruction::Int(i)];

            let mut vm = VM::default();
            vm.exec(&program, &mut shell).unwrap();
        }
    }

    #[test]
    #[should_panic]
    fn mem_too_small() {
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();
        program.mem_size = Some(1);

        let mut vm = VM::default();
        vm.exec(&program, &mut shell).unwrap();
    }

    #[test] // TODO: This should be removed in the future
    fn all_instructions() {
        let instr = vec![
            Instruction::Neg(IntegerType::U16),
            Instruction::Shr(IntegerType::U16),
            Instruction::Shl(IntegerType::U16),
            Instruction::And(IntegerType::U16),
            Instruction::Or(IntegerType::U16),
            Instruction::Xor(IntegerType::U16),
            Instruction::Not(IntegerType::U16),
            Instruction::Cmp(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
            Instruction::U8Promote,
            Instruction::U16Demote,
            Instruction::I8Promote,
            Instruction::I16Demote,
            Instruction::Dup(IntegerType::U16),
            Instruction::Drop(IntegerType::U16),
            Instruction::Int(12),
            Instruction::Ret,
            Instruction::Jmp(0),
            Instruction::Jnz(0),
            Instruction::Jz(0),
            Instruction::Jn(0),
            Instruction::Jp(0),
            Instruction::Call(0xABCD),
        ];

        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();
        program.instructions = instr;

        let mut vm = VM::default();
        let err = vm.exec(&program, &mut shell).err().expect("error expected");
        let formatted_err = format!("{}", err);

        assert!(formatted_err.starts_with("instruction"));
        assert!(formatted_err.ends_with("not yet implemented"));
    }

    #[test]
    fn push_load_store() {
        let instr = vec![
            Instruction::PushConstU8(1),
            Instruction::PushConstU16(2),
            Instruction::PushConstI8(3),
            Instruction::PushConstI16(4),
            Instruction::Store(IntegerType::I16, 0xABDC),
            Instruction::Store(IntegerType::I8, 0xBACD),
            Instruction::Store(IntegerType::U16, 0xACBD),
            Instruction::Store(IntegerType::U8, 0xABCD),
            Instruction::Load(IntegerType::U8, 0xABCD),
            Instruction::Load(IntegerType::U16, 0xACBD),
            Instruction::Load(IntegerType::I8, 0xBACD),
            Instruction::Load(IntegerType::I16, 0xABDC),
        ];

        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();
        program.instructions = instr;

        let mut vm = VM::default();
        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 4);
        assert_eq!(vm.pop_i8().unwrap(), 3);
        assert_eq!(vm.pop_u16().unwrap(), 2);
        assert_eq!(vm.pop_u8().unwrap(), 1);
    }

    #[test]
    fn add_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(50),
            Instruction::PushConstU8(50),
            Instruction::Add(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 100);

        program.instructions = vec![
            Instruction::PushConstU16(2500),
            Instruction::PushConstU16(1000),
            Instruction::Add(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 3500);

        program.instructions = vec![
            Instruction::PushConstI8(50),
            Instruction::PushConstI8(-20),
            Instruction::Add(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 30);

        program.instructions = vec![
            Instruction::PushConstI16(50),
            Instruction::PushConstI16(1000),
            Instruction::Add(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 1050);
    }

    #[test]
    fn sub_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(100),
            Instruction::PushConstU8(50),
            Instruction::Sub(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 50);

        program.instructions = vec![
            Instruction::PushConstU16(2500),
            Instruction::PushConstU16(1000),
            Instruction::Sub(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 1500);

        program.instructions = vec![
            Instruction::PushConstI8(50),
            Instruction::PushConstI8(100),
            Instruction::Sub(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -50);

        program.instructions = vec![
            Instruction::PushConstI16(50),
            Instruction::PushConstI16(1000),
            Instruction::Sub(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -950);
    }

    #[test]
    fn mul_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(8),
            Instruction::PushConstU8(8),
            Instruction::Mul(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 64);

        program.instructions = vec![
            Instruction::PushConstU16(150),
            Instruction::PushConstU16(150),
            Instruction::Mul(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 22500);

        program.instructions = vec![
            Instruction::PushConstI8(13),
            Instruction::PushConstI8(-4),
            Instruction::Mul(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -52);

        program.instructions = vec![
            Instruction::PushConstI16(-50),
            Instruction::PushConstI16(100),
            Instruction::Mul(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -5000);
    }

    #[test]
    fn div_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(8),
            Instruction::PushConstU8(4),
            Instruction::Div(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 2);

        program.instructions = vec![
            Instruction::PushConstU16(1500),
            Instruction::PushConstU16(500),
            Instruction::Div(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 3);

        program.instructions = vec![
            Instruction::PushConstI8(13),
            Instruction::PushConstI8(-4),
            Instruction::Div(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -3);

        program.instructions = vec![
            Instruction::PushConstI16(1000),
            Instruction::PushConstI16(-50),
            Instruction::Div(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -20);
    }

    #[test]
    fn shr_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(8),
            Instruction::PushConstU8(3),
            Instruction::Shr(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 1);

        program.instructions = vec![
            Instruction::PushConstU16(16),
            Instruction::PushConstU16(1),
            Instruction::Shr(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 8);

        program.instructions = vec![
            Instruction::PushConstI8(32),
            Instruction::PushConstI8(2),
            Instruction::Shr(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 8);

        program.instructions = vec![
            Instruction::PushConstI16(128),
            Instruction::PushConstI16(4),
            Instruction::Shr(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 8);
    }

    #[test]
    fn shl_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(1),
            Instruction::PushConstU8(4),
            Instruction::Shl(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 16);

        program.instructions = vec![
            Instruction::PushConstU16(1),
            Instruction::PushConstU16(8),
            Instruction::Shl(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 256);

        program.instructions = vec![
            Instruction::PushConstI8(1),
            Instruction::PushConstI8(3),
            Instruction::Shl(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 8);

        program.instructions = vec![
            Instruction::PushConstI16(1),
            Instruction::PushConstI16(2),
            Instruction::Shl(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 4);
    }

    #[test]
    fn and_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(0b01010101),
            Instruction::PushConstU8(0xFF),
            Instruction::And(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0b01010101);

        program.instructions = vec![
            Instruction::PushConstU16(0b1010101010101010),
            Instruction::PushConstU16(0xFFFF),
            Instruction::And(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0b1010101010101010);

        program.instructions = vec![
            Instruction::PushConstI8(0b0101),
            Instruction::PushConstI8(0x0F),
            Instruction::And(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 0b0101);

        program.instructions = vec![
            Instruction::PushConstI16(0b01010101),
            Instruction::PushConstI16(0xFF),
            Instruction::And(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0b01010101);
    }

    #[test]
    fn or_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(0xFF),
            Instruction::PushConstU8(0x00),
            Instruction::Or(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0xFF);

        program.instructions = vec![
            Instruction::PushConstU16(0xFF00),
            Instruction::PushConstU16(0x00FF),
            Instruction::Or(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0xFFFF);

        program.instructions = vec![
            Instruction::PushConstI8(0x0F),
            Instruction::PushConstI8(0x00),
            Instruction::Or(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 0x0F);

        program.instructions = vec![
            Instruction::PushConstI16(0x00FF),
            Instruction::PushConstI16(0x0000),
            Instruction::Or(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0x00FF);
    }

    #[test]
    fn xor_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(0xFF),
            Instruction::PushConstU8(0x00),
            Instruction::Xor(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0xFF);

        program.instructions = vec![
            Instruction::PushConstU16(0xFF00),
            Instruction::PushConstU16(0x00FF),
            Instruction::Xor(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0xFFFF);

        program.instructions = vec![
            Instruction::PushConstI8(0x0F),
            Instruction::PushConstI8(0x00),
            Instruction::Xor(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 0x0F);

        program.instructions = vec![
            Instruction::PushConstI16(0x00FF),
            Instruction::PushConstI16(0x0000),
            Instruction::Xor(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0x00FF);
    }
}
