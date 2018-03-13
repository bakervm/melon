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
    /// The Result of the last comparison
    cmp_res: i32,
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

        if let Some(num_pages) = program.num_pages {
            ensure!(num_pages <= MAX_MEM_PAGE_COUNT, "requested memory too big");

            ensure!(num_pages > 0, "requested memory too small");
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

        let mem_size = program.num_pages.unwrap_or(DEFAULT_MEM_PAGE_COUNT) * MEM_PAGE;

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
            Instruction::Not(ty) => self.not(ty)?,
            Instruction::Neg(ty) => self.neg(ty)?,
            Instruction::Cmp(ty) => self.cmp(ty)?,
            Instruction::Inc(ty) => self.inc(ty)?,
            Instruction::Dec(ty) => self.dec(ty)?,
            Instruction::U8Promote => self.u8_promote()?,
            Instruction::U16Demote => self.u16_demote()?,
            Instruction::I8Promote => self.i8_promote()?,
            Instruction::I16Demote => self.i16_demote()?,
            Instruction::PushConstU8(value) => self.push_const_u8(value)?,
            Instruction::PushConstU16(value) => self.push_const_u16(value)?,
            Instruction::PushConstI8(value) => self.push_const_i8(value)?,
            Instruction::PushConstI16(value) => self.push_const_i16(value)?,
            Instruction::LoadReg(reg) => self.load_reg(reg)?,
            Instruction::Load(ty, addr) => self.load(ty, addr)?,
            Instruction::LoadIndirect(ty) => self.load_indirect(ty)?,
            Instruction::Store(ty, addr) => self.store(ty, addr)?,
            Instruction::StoreIndirect(ty) => self.store_indirect(ty)?,
            Instruction::Dup(ty) => self.dup(ty)?,
            Instruction::Drop(ty) => self.drop(ty)?,
            Instruction::Int(0) => self.halt(),
            Instruction::Int(signal) => shell.int(self, signal)?,
            // Instruction::Call(addr) => self.call(addr),
            // Instruction::Ret => self.ret(),
            Instruction::Jmp(int) => self.jmp(int)?,
            Instruction::Jnz(int) => self.jnz(int)?,
            Instruction::Jz(int) => self.jz(int)?,
            Instruction::Jn(int) => self.jn(int)?,
            Instruction::Jp(int) => self.jp(int)?,
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

    /// Applies a *bitwise not* operation to the top stack value
    pub fn not(&mut self, ty: IntegerType) -> Result<()> {
        let addr = self.sp;

        match ty {
            IntegerType::U8 | IntegerType::I8 => {
                let value = self.read_u8(addr)?;
                self.write_u8(addr, !value)
            }
            IntegerType::U16 | IntegerType::I16 => {
                let value = self.read_u16(addr)?;
                self.write_u16(addr, !value)
            }
        }
    }

    /// Applies a *negation* on the tio stack value
    pub fn neg(&mut self, ty: IntegerType) -> Result<()> {
        let addr = self.sp;

        match ty {
            IntegerType::I8 => {
                let value = self.read_u8(addr)?;
                let converted = -(value as SmallInt);

                self.write_u8(addr, converted as SmallUInt)
            }
            IntegerType::I16 => {
                let value = self.read_u16(addr)?;
                let converted = -(value as Int);

                self.write_u16(addr, converted as UInt)
            }
            IntegerType::U8 => bail!("unable to create negative u8"),
            IntegerType::U16 => bail!("unable to create negative u16"),
        }
    }

    /// *Compares* the top two values of the stack by applying a subtraction on them and saving the
    /// result in the cmp register
    pub fn cmp(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                let (a, b) = self.pop_u8_lr()?;
                self.cmp_res = (a - b) as i32;
                self.push_const_u8(a)?;
                self.push_const_u8(b)?;
            }
            IntegerType::U16 => {
                let (a, b) = self.pop_u16_lr()?;
                self.cmp_res = (a - b) as i32;
                self.push_const_u16(a)?;
                self.push_const_u16(b)?;
            }
            IntegerType::I8 => {
                let (a, b) = self.pop_i8_lr()?;
                self.cmp_res = (a - b) as i32;
                self.push_const_i8(a)?;
                self.push_const_i8(b)?;
            }
            IntegerType::I16 => {
                let (a, b) = self.pop_i16_lr()?;
                self.cmp_res = (a - b) as i32;
                self.push_const_i16(a)?;
                self.push_const_i16(b)?;
            }
        }

        Ok(())
    }

    /// *Increments* the top stack value
    pub fn inc(&mut self, ty: IntegerType) -> Result<()> {
        let addr = self.sp;

        match ty {
            IntegerType::U8 => {
                let value = self.read_u8(addr)?;
                self.write_u8(addr, value + 1)
            }
            IntegerType::U16 => {
                let value = self.read_u16(addr)?;
                self.write_u16(addr, value + 1)
            }
            IntegerType::I8 => {
                let value = self.read_u8(addr)? as SmallInt;
                self.write_u8(addr, (value + 1) as SmallUInt)
            }
            IntegerType::I16 => {
                let value = self.read_u16(addr)? as Int;
                self.write_u16(addr, (value + 1) as UInt)
            }
        }
    }

    /// *Decrements* the top stack value
    pub fn dec(&mut self, ty: IntegerType) -> Result<()> {
        let addr = self.sp;

        match ty {
            IntegerType::U8 => {
                let value = self.read_u8(addr)?;
                self.write_u8(addr, value - 1)
            }
            IntegerType::U16 => {
                let value = self.read_u16(addr)?;
                self.write_u16(addr, value - 1)
            }
            IntegerType::I8 => {
                let value = self.read_u8(addr)? as SmallInt;
                self.write_u8(addr, (value - 1) as SmallUInt)
            }
            IntegerType::I16 => {
                let value = self.read_u16(addr)? as Int;
                self.write_u16(addr, (value - 1) as UInt)
            }
        }
    }

    /// Converts a u8 to a u16
    pub fn u8_promote(&mut self) -> Result<()> {
        let value = self.pop_u8()?;

        self.push_const_u16(value as UInt)
    }

    /// Converts a u16 to a u8
    pub fn u16_demote(&mut self) -> Result<()> {
        let value = self.pop_u16()?;

        self.push_const_u8(value as SmallUInt)
    }

    /// Converts a i8 to a i16
    pub fn i8_promote(&mut self) -> Result<()> {
        let value = self.pop_i8()?;

        self.push_const_i16(value as Int)
    }

    /// Converts a i16 to a i8
    pub fn i16_demote(&mut self) -> Result<()> {
        let value = self.pop_i16()?;

        self.push_const_i8(value as SmallInt)
    }

    /// Pushes the given u8 onto the stack
    pub fn push_const_u8(&mut self, value: SmallUInt) -> Result<()> {
        self.sp -= 1;

        let addr = self.sp;

        self.write_u8(addr, value)
    }

    /// Pushes the given u16 onto the stack
    pub fn push_const_u16(&mut self, value: UInt) -> Result<()> {
        self.sp -= 2;

        let addr = self.sp;

        self.write_u16(addr, value)
    }

    /// Pushes the given i8 onto the stack
    pub fn push_const_i8(&mut self, value: SmallInt) -> Result<()> {
        self.sp -= 1;

        let addr = self.sp;

        self.write_u8(addr, value as SmallUInt)
    }

    /// Pushes the given i16 onto the stack
    pub fn push_const_i16(&mut self, value: Int) -> Result<()> {
        self.sp -= 2;

        let addr = self.sp;

        self.write_u16(addr, value as UInt)
    }

    /// Loads the value from the given register and pushes it onto the stack
    pub fn load_reg(&mut self, reg: Register) -> Result<()> {
        let ptr = match reg {
            Register::StackPtr => self.sp,
            Register::BasePtr => self.bp,
        };

        self.push_const_u16(ptr)
    }

    /// Loads the value from the given address and pushes it to the stack
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

    /// Like *load* but takes the address off the stack before storing
    pub fn load_indirect(&mut self, ty: IntegerType) -> Result<()> {
        let addr = self.pop_u16()?;
        self.load(ty, addr)?;

        Ok(())
    }

    /// Takes the top value off the stack and stores it at the given address
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

    /// Like *store* but takes the address off the stack before storing
    pub fn store_indirect(&mut self, ty: IntegerType) -> Result<()> {
        let addr = self.pop_u16()?;
        self.store(ty, addr)?;

        Ok(())
    }

    /// Duplicates the top stack value and pushes it onto the stack
    pub fn dup(&mut self, ty: IntegerType) -> Result<()> {
        let addr = self.sp;

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

    /// Discards the top stack value
    pub fn drop(&mut self, ty: IntegerType) -> Result<()> {
        match ty {
            IntegerType::U8 => {
                self.pop_u8()?;
            }
            IntegerType::U16 => {
                self.pop_u16()?;
            }
            IntegerType::I8 => {
                self.pop_i8()?;
            }
            IntegerType::I16 => {
                self.pop_i16()?;
            }
        }

        Ok(())
    }

    /// Jumps unconditionally in the given direction
    pub fn jmp(&mut self, dir: Int) -> Result<()> {
        ensure!(dir != 0, "relative jumps nowhere will hang the program");
        // The (-1) is because the program counter has already been advanced
        let addr = ((self.pc as Int) - 1) + dir;
        self.pc = addr as Address;

        Ok(())
    }

    /// Jumps if the value of the cmp register is not zero, in the given direction
    pub fn jnz(&mut self, dir: Int) -> Result<()> {
        if self.cmp_res != 0 {
            self.jmp(dir)?;
        }

        Ok(())
    }

    /// Jumps if the value of the cmp register is zero, in the given direction
    pub fn jz(&mut self, dir: Int) -> Result<()> {
        if self.cmp_res == 0 {
            self.jmp(dir)?;
        }

        Ok(())
    }

    /// Jumps if the value of the cmp register is negative, in the given direction
    pub fn jn(&mut self, dir: Int) -> Result<()> {
        if self.cmp_res.is_negative() {
            self.jmp(dir)?;
        }

        Ok(())
    }

    /// Jumps if the value of the cmp register is positive, in the given direction
    pub fn jp(&mut self, dir: Int) -> Result<()> {
        if self.cmp_res.is_positive() {
            self.jmp(dir)?;
        }

        Ok(())
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
                num_pages: Some(63),
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
        program.num_pages = Some(1);

        let mut vm = VM::default();
        vm.exec(&program, &mut shell).unwrap();
    }

    #[test] // TODO: This should be removed in the future
    fn all_instructions() {
        let instr = vec![Instruction::Ret, Instruction::Call(0xABCD)];

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

    #[test]
    fn not_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(0x0F),
            Instruction::Not(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0xF0);

        program.instructions = vec![
            Instruction::PushConstU16(0xFF00),
            Instruction::Not(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0x00FF);

        program.instructions = vec![
            Instruction::PushConstI8(0x0F),
            Instruction::Not(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0xF0);

        program.instructions = vec![
            Instruction::PushConstI16(0x00FF),
            Instruction::Not(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0xFF00);
    }

    #[test]
    fn neg_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstI8(104),
            Instruction::Neg(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -104);

        program.instructions = vec![
            Instruction::PushConstI16(-1234),
            Instruction::Neg(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 1234);

        program.instructions = vec![Instruction::Neg(IntegerType::U8)];

        assert!(vm.exec(&program, &mut shell).is_err());

        program.instructions = vec![Instruction::Neg(IntegerType::U16)];

        assert!(vm.exec(&program, &mut shell).is_err());
    }

    #[test]
    fn cmp_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(104),
            Instruction::PushConstU8(98),
            Instruction::Cmp(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.cmp_res, 6);
        assert_eq!(vm.pop_u8().unwrap(), 98);
        assert_eq!(vm.pop_u8().unwrap(), 104);

        program.instructions = vec![
            Instruction::PushConstU16(20000),
            Instruction::PushConstU16(20000),
            Instruction::Cmp(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.cmp_res, 0);
        assert_eq!(vm.pop_u16().unwrap(), 20000);
        assert_eq!(vm.pop_u16().unwrap(), 20000);

        program.instructions = vec![
            Instruction::PushConstI8(-32),
            Instruction::PushConstI8(-64),
            Instruction::Cmp(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.cmp_res, 32);
        assert_eq!(vm.pop_i8().unwrap(), -64);
        assert_eq!(vm.pop_i8().unwrap(), -32);

        program.instructions = vec![
            Instruction::PushConstI16(-3200),
            Instruction::PushConstI16(-6400),
            Instruction::Cmp(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.cmp_res, 3200);
        assert_eq!(vm.pop_i16().unwrap(), -6400);
        assert_eq!(vm.pop_i16().unwrap(), -3200);
    }

    #[test]
    fn inc_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(100),
            Instruction::Inc(IntegerType::U8),
            Instruction::Inc(IntegerType::U8),
            Instruction::Inc(IntegerType::U8),
            Instruction::Inc(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 104);

        program.instructions = vec![
            Instruction::PushConstU16(20000),
            Instruction::Inc(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 20005);

        program.instructions = vec![
            Instruction::PushConstI8(-32),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
            Instruction::Inc(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -16);

        program.instructions = vec![
            Instruction::PushConstI16(-4),
            Instruction::Inc(IntegerType::I16),
            Instruction::Inc(IntegerType::I16),
            Instruction::Inc(IntegerType::I16),
            Instruction::Inc(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0);
    }

    #[test]
    fn dec_instruction() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(100),
            Instruction::Dec(IntegerType::U8),
            Instruction::Dec(IntegerType::U8),
            Instruction::Dec(IntegerType::U8),
            Instruction::Dec(IntegerType::U8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 96);

        program.instructions = vec![
            Instruction::PushConstU16(20000),
            Instruction::Dec(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 19995);

        program.instructions = vec![
            Instruction::PushConstI8(32),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
            Instruction::Dec(IntegerType::I8),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 16);

        program.instructions = vec![
            Instruction::PushConstI16(4),
            Instruction::Dec(IntegerType::I16),
            Instruction::Dec(IntegerType::I16),
            Instruction::Dec(IntegerType::I16),
            Instruction::Dec(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0);
    }

    #[test]
    fn promotion_demotion() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![Instruction::PushConstU8(90), Instruction::U8Promote];
        vm.exec(&program, &mut shell).unwrap();
        assert_eq!(vm.pop_u16().unwrap(), 90);

        program.instructions = vec![Instruction::PushConstU16(190), Instruction::U16Demote];
        vm.exec(&program, &mut shell).unwrap();
        assert_eq!(vm.pop_u8().unwrap(), 190);

        program.instructions = vec![Instruction::PushConstI8(-90), Instruction::I8Promote];
        vm.exec(&program, &mut shell).unwrap();
        assert_eq!(vm.pop_i16().unwrap(), -90);

        program.instructions = vec![Instruction::PushConstI16(-120), Instruction::I16Demote];
        vm.exec(&program, &mut shell).unwrap();
        assert_eq!(vm.pop_i8().unwrap(), -120);
    }

    #[test]
    fn jumps() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::Jmp(6),
            Instruction::Jp(1),
            Instruction::Jn(1),
            Instruction::Jz(1),
            Instruction::Jnz(1),
            Instruction::Jmp(2),
            Instruction::Jmp(-5),
        ];

        vm.exec(&program, &mut shell).unwrap();

        program.instructions = vec![Instruction::Jmp(1), Instruction::Jp(1)];
        vm.cmp_res = 1;
        vm.exec(&program, &mut shell).unwrap();

        program.instructions = vec![Instruction::Jmp(1), Instruction::Jn(1)];
        vm.cmp_res = -1;
        vm.exec(&program, &mut shell).unwrap();

        program.instructions = vec![Instruction::Jmp(1), Instruction::Jz(1)];
        vm.cmp_res = 0;
        vm.exec(&program, &mut shell).unwrap();

        program.instructions = vec![Instruction::Jmp(1), Instruction::Jnz(1)];
        vm.cmp_res = 1234;
        vm.exec(&program, &mut shell).unwrap();
    }

    #[test]
    fn indirect_addr() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstI16(-1234),
            Instruction::PushConstU16(0x0FFF),
            Instruction::StoreIndirect(IntegerType::I16),
            Instruction::PushConstU16(0x0FFF - 1),
            Instruction::PushConstU16(1),
            Instruction::Add(IntegerType::U16),
            Instruction::LoadIndirect(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -1234);
    }

    #[test]
    fn dup_drop() {
        let mut vm = VM::default();
        let mut shell = helper::generate_shell();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstI16(-1234),
            Instruction::PushConstU16(0x0FFF),
            Instruction::Drop(IntegerType::U16),
            Instruction::Dup(IntegerType::I16),
        ];

        vm.exec(&program, &mut shell).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -1234);
    }
}
