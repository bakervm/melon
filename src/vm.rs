use byteorder::{BigEndian, ByteOrder};
use failure::ResultExt;
use instruction::{Instruction, IntegerType, Register};
use program::Program;
use std::collections::LinkedList;
use system::System;
use typedef::*;

type Endianess = BigEndian;

/// The size of a memory page in bytes
pub const MEM_PAGE: usize = 1024;
/// The default number of pages allocated by the VM
const DEFAULT_MEM_PAGE_COUNT: u8 = 32;
/// The maimum number of pages that can be allocated by the VM
const MAX_MEM_PAGE_COUNT: u8 = 64;

/// The state of the VM
#[derive(Serialize, Deserialize, Default, Debug)]
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
    /// The stack of calls (return addresses)
    call_stack: LinkedList<Address>,
    /// The stack of previous allocations
    alloc_stack: LinkedList<UInt>,
    /// The Result of the last comparison
    cmp_res: i32,
    halted: bool,
}

impl VM {
    /// Executes the given program using the given system and returns the program's exit status
    pub fn exec<T: System>(&mut self, program: &Program, system: &mut T) -> Result<SmallUInt> {
        self.reset::<T>(&program)?;

        system.prepare(self)?;

        while (self.pc < self.program.len() as Address) && !self.halted {
            system.pre_cycle(self)?;

            self.do_cycle(system)?;

            system.post_cycle(self)?;
        }

        system.finish(self)?;

        Ok(self.return_value)
    }

    /// Resets the VM to its default state
    fn reset<T: System>(&mut self, program: &Program) -> Result<()> {
        *self = Default::default();

        ensure!(
            program.system_id == T::ID,
            "wrong system ID. Runtime: {:?} Program: {:?}",
            T::ID,
            program.system_id
        );

        ensure!(
            program.target_version == env!("CARGO_PKG_VERSION"),
            "wrong core version. Runtime: {:?} Program: {:?}",
            env!("CARGO_PKG_VERSION"),
            program.target_version
        );

        if let Some(mem_pages) = program.mem_pages {
            ensure!(
                (mem_pages + T::MEM_PAGES) <= MAX_MEM_PAGE_COUNT,
                "requested memory too big. Requested pages: {}. Maximum number of pages: {}",
                (mem_pages + T::MEM_PAGES),
                MAX_MEM_PAGE_COUNT
            );

            ensure!(
                mem_pages > 0,
                "requested memory too small. Number of memory pages has to be at least one"
            );
        }

        ensure!(
            program.instructions.len() <= (UInt::max_value() as usize),
            "program has too many instructions. Maximum number of instructions: {}",
            UInt::max_value()
        );

        ensure!(
            program.instructions.is_empty()
                || (program.entry_point as usize) < program.instructions.len(),
            "entry point does not point to a valid instruction"
        );

        let mem_pages = program.mem_pages.unwrap_or(DEFAULT_MEM_PAGE_COUNT) + T::MEM_PAGES;
        let mem_size: usize = (mem_pages as usize) * MEM_PAGE;

        self.program = program.instructions.clone();
        self.mem = vec![0; mem_size];
        self.sp = (self.mem.len() - 1) as Address;
        self.pc = program.entry_point;

        Ok(())
    }

    /// Advances the program counter
    fn advance_pc(&mut self) {
        self.pc += 1;
    }

    /// Returns the current value of the program counter
    pub fn pc(&mut self) -> Address {
        self.pc
    }

    /// Returns the current value of the stack pointer
    pub fn sp(&mut self) -> Address {
        self.sp
    }

    /// Returns the current value of the base pointer
    pub fn bp(&mut self) -> Address {
        self.bp
    }

    /// Returns the instruction at the current pc
    pub fn current_instruction(&mut self) -> Result<Instruction> {
        if let Some(current_instruction) = self.program.get(self.pc as usize) {
            Ok(current_instruction.clone())
        } else {
            bail!("could no find instruction at ${:04X}", self.pc);
        }
    }

    /// Consume and execute a single instruction
    fn handle_instruction<T: System>(
        &mut self,
        instruction: Instruction,
        system: &mut T,
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
            Instruction::SysCall(0) => self.halt(),
            Instruction::SysCall(signal) => system.system_call(self, signal)?,
            Instruction::Call(addr) => self.call(addr),
            Instruction::Ret => self.ret()?,
            Instruction::Alloc(amount) => self.alloc(amount)?,
            Instruction::Free => self.free()?,
            Instruction::Jmp(forward, addr) => self.jmp(forward, addr)?,
            Instruction::Jnz(forward, addr) => self.jnz(forward, addr)?,
            Instruction::Jz(forward, addr) => self.jz(forward, addr)?,
            Instruction::Jn(forward, addr) => self.jn(forward, addr)?,
            Instruction::Jp(forward, addr) => self.jp(forward, addr)?,
        }

        Ok(())
    }

    /// Runs one execution cycle
    fn do_cycle<T: System>(&mut self, system: &mut T) -> Result<()> {
        let current_instruction = self.current_instruction()?;

        self.advance_pc();

        self.handle_instruction(current_instruction, system)?;

        Ok(())
    }

    /// Stops execution and shuts down the VM
    pub fn halt(&mut self) {
        self.halted = true;
    }

    /// Helper function to ensure the validity of a memory address
    fn ensure_valid_mem_addr(&mut self, addr: Address) -> Result<()> {
        ensure!(
            addr < ((self.mem.len() - 1) as Address),
            "memory address out of bounds"
        );

        Ok(())
    }

    /// Checks the VM state for a heap crash and returns an error if so
    fn detect_heap_crash(&mut self) -> Result<()> {
        ensure!(
            self.bp < self.sp,
            "heap crash detected! Heap cannot overlap with stack"
        );

        Ok(())
    }

    /// Returns the u8 at the given address
    pub fn read_u8(&mut self, addr: Address) -> Result<SmallUInt> {
        self.ensure_valid_mem_addr(addr)?;

        Ok(self.mem[addr as usize])
    }

    /// Writes the given u8 to the given address
    pub fn write_u8(&mut self, addr: Address, value: SmallUInt) -> Result<()> {
        self.ensure_valid_mem_addr(addr)?;

        self.mem[addr as usize] = value;

        Ok(())
    }

    /// Returns the u16 at the given address
    pub fn read_u16(&mut self, addr: Address) -> Result<UInt> {
        self.ensure_valid_mem_addr(addr + 1)?;

        let inner_addr_start = addr as usize;

        let value = <Endianess as ByteOrder>::read_u16(&self.mem[inner_addr_start..]);

        Ok(value)
    }

    /// Writes the given u16 to the given address
    pub fn write_u16(&mut self, addr: Address, value: UInt) -> Result<()> {
        self.ensure_valid_mem_addr(addr + 1)?;

        let inner_addr_start = addr as usize;

        <Endianess as ByteOrder>::write_u16(&mut self.mem[inner_addr_start..], value);

        Ok(())
    }

    /// Helper method for popping a u8 value off the stack
    pub fn pop_u8(&mut self) -> Result<SmallUInt> {
        let addr = self.sp;

        let value = self.read_u8(addr)
            .context("cannot pop a value off an empty stack")?;

        self.sp += 1;

        Ok(value)
    }

    /// Helper method for popping a u16 value off the stack
    pub fn pop_u16(&mut self) -> Result<UInt> {
        let addr = self.sp;

        let value = self.read_u16(addr)
            .context("cannot pop a value off an empty stack")?;

        self.sp += 2;

        Ok(value)
    }

    /// Helper method for popping a i8 value off the stack
    pub fn pop_i8(&mut self) -> Result<SmallInt> {
        let addr = self.sp;

        let value = self.read_u8(addr)
            .context("cannot pop a value off an empty stack")?;

        self.sp += 1;

        Ok(value as SmallInt)
    }

    /// Helper method for popping a i16 value off the stack
    pub fn pop_i16(&mut self) -> Result<Int> {
        let addr = self.sp;

        let value = self.read_u16(addr)
            .context("cannot pop a value off an empty stack")?;

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

        self.detect_heap_crash()?;

        let addr = self.sp;

        self.write_u8(addr, value)
    }

    /// Pushes the given u16 onto the stack
    pub fn push_const_u16(&mut self, value: UInt) -> Result<()> {
        self.sp -= 2;

        self.detect_heap_crash()?;

        let addr = self.sp;

        self.write_u16(addr, value)
    }

    /// Pushes the given i8 onto the stack
    pub fn push_const_i8(&mut self, value: SmallInt) -> Result<()> {
        self.sp -= 1;

        self.detect_heap_crash()?;

        let addr = self.sp;

        self.write_u8(addr, value as SmallUInt)
    }

    /// Pushes the given i16 onto the stack
    pub fn push_const_i16(&mut self, value: Int) -> Result<()> {
        self.sp -= 2;

        self.detect_heap_crash()?;

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

    /// Calls the function at the given address
    pub fn call(&mut self, addr: Address) {
        let call = self.pc;
        self.call_stack.push_front(call);
        self.pc = addr;
    }

    /// Returns from a function call
    pub fn ret(&mut self) -> Result<()> {
        let return_addr = self.call_stack
            .pop_front()
            .ok_or(format_err!("cannot return from an empty call stack"))?;

        self.pc = return_addr;

        Ok(())
    }

    /// Allocates the given number of bytes in the heap
    pub fn alloc(&mut self, amount: UInt) -> Result<()> {
        self.alloc_stack.push_front(amount);
        self.bp += amount;

        self.detect_heap_crash()?;

        Ok(())
    }

    /// Undos the last allocation and frees the memory
    pub fn free(&mut self) -> Result<()> {
        let amount = self.alloc_stack
            .pop_front()
            .ok_or(format_err!("cannot free unallocated memory"))?;

        self.bp -= amount;

        Ok(())
    }

    /// Jumps unconditionally in the given direction
    pub fn jmp(&mut self, forward: bool, addr: Address) -> Result<()> {
        ensure!(
            addr != (self.pc - 1),
            "jumps to nowhere will hang the program"
        );

        // Bring the program counter back to the original position
        self.pc -= 1;

        if forward {
            self.pc += addr;
        } else {
            self.pc -= addr;
        }

        Ok(())
    }

    /// Jumps if the value of the cmp register is not zero, in the given direction
    pub fn jnz(&mut self, forward: bool, addr: Address) -> Result<()> {
        if self.cmp_res != 0 {
            self.jmp(forward, addr)?;
        }

        Ok(())
    }

    /// Jumps if the value of the cmp register is zero, in the given direction
    pub fn jz(&mut self, forward: bool, addr: Address) -> Result<()> {
        if self.cmp_res == 0 {
            self.jmp(forward, addr)?;
        }

        Ok(())
    }

    /// Jumps if the value of the cmp register is negative, in the given direction
    pub fn jn(&mut self, forward: bool, addr: Address) -> Result<()> {
        if self.cmp_res.is_negative() {
            self.jmp(forward, addr)?;
        }

        Ok(())
    }

    /// Jumps if the value of the cmp register is positive, in the given direction
    pub fn jp(&mut self, forward: bool, addr: Address) -> Result<()> {
        if self.cmp_res.is_positive() {
            self.jmp(forward, addr)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use instruction::{Instruction, IntegerType};
    use rand::{self, Rng};

    mod helper {
        use instruction::{Instruction, IntegerType, Register};
        use program::Program;
        use system::System;

        #[derive(Default)]
        pub struct BogusSystem {
            _data: [u8; 8],
        }

        impl System for BogusSystem {
            const ID: &'static str = "__BOGUS_SYSTEM__";

            const MEM_PAGES: u8 = 1;
        }

        pub fn generate_system() -> BogusSystem {
            Default::default()
        }

        pub fn generate_program() -> Program {
            Program {
                target_version: env!("CARGO_PKG_VERSION").to_owned(),
                system_id: BogusSystem::ID.to_owned(),
                instructions: generate_instructions(),
                mem_pages: Some(63),
                entry_point: 0,
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
                Instruction::SysCall(123),
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
        vm.reset::<helper::BogusSystem>(&helper::generate_program())
            .unwrap();

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
        vm.reset::<helper::BogusSystem>(&helper::generate_program())
            .unwrap();

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
        vm.reset::<helper::BogusSystem>(&helper::generate_program())
            .unwrap();

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
        vm.reset::<helper::BogusSystem>(&helper::generate_program())
            .unwrap();

        let mut rng = rand::thread_rng();

        for _ in 0..300 {
            let test_value = rng.gen();

            vm.push_const_i16(test_value).unwrap();
            assert_eq!(vm.pop_i16().unwrap(), test_value);
        }
    }

    #[test]
    fn simple_execution() {
        let mut system = helper::generate_system();
        let program = helper::generate_program();

        let mut vm = VM::default();
        vm.exec(&program, &mut system).unwrap();
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
        let mut system = helper::generate_system();
        let program = helper::generate_program();

        let mut vm = VM::default();
        vm.pc = (program.instructions.len() + 20) as Address;

        vm.exec(&program, &mut system).unwrap();
    }

    #[test]
    fn int_exec() {
        for i in 0..300 {
            let mut system = helper::generate_system();
            let mut program = helper::generate_program();
            program.instructions = vec![Instruction::SysCall(i)];

            let mut vm = VM::default();
            vm.exec(&program, &mut system).unwrap();
        }
    }

    #[test]
    #[should_panic]
    fn mem_too_small() {
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();
        program.mem_pages = Some(1);

        let mut vm = VM::default();
        vm.exec(&program, &mut system).unwrap();
    }

    #[test]
    #[should_panic]
    fn mem_too_big() {
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();
        program.mem_pages = Some(MAX_MEM_PAGE_COUNT + 1);

        let mut vm = VM::default();
        vm.exec(&program, &mut system).unwrap();
    }

    #[test]
    #[should_panic]
    fn program_too_big() {
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![Instruction::SysCall(123); (UInt::max_value() as usize) + 2];

        let mut vm = VM::default();
        vm.exec(&program, &mut system).unwrap();
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

        let mut system = helper::generate_system();
        let mut program = helper::generate_program();
        program.instructions = instr;

        let mut vm = VM::default();
        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 4);
        assert_eq!(vm.pop_i8().unwrap(), 3);
        assert_eq!(vm.pop_u16().unwrap(), 2);
        assert_eq!(vm.pop_u8().unwrap(), 1);
    }

    #[test]
    fn add_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(50),
            Instruction::PushConstU8(50),
            Instruction::Add(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 100);

        program.instructions = vec![
            Instruction::PushConstU16(2500),
            Instruction::PushConstU16(1000),
            Instruction::Add(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 3500);

        program.instructions = vec![
            Instruction::PushConstI8(50),
            Instruction::PushConstI8(-20),
            Instruction::Add(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 30);

        program.instructions = vec![
            Instruction::PushConstI16(50),
            Instruction::PushConstI16(1000),
            Instruction::Add(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 1050);
    }

    #[test]
    fn sub_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(100),
            Instruction::PushConstU8(50),
            Instruction::Sub(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 50);

        program.instructions = vec![
            Instruction::PushConstU16(2500),
            Instruction::PushConstU16(1000),
            Instruction::Sub(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 1500);

        program.instructions = vec![
            Instruction::PushConstI8(50),
            Instruction::PushConstI8(100),
            Instruction::Sub(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -50);

        program.instructions = vec![
            Instruction::PushConstI16(50),
            Instruction::PushConstI16(1000),
            Instruction::Sub(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -950);
    }

    #[test]
    fn mul_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(8),
            Instruction::PushConstU8(8),
            Instruction::Mul(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 64);

        program.instructions = vec![
            Instruction::PushConstU16(150),
            Instruction::PushConstU16(150),
            Instruction::Mul(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 22500);

        program.instructions = vec![
            Instruction::PushConstI8(13),
            Instruction::PushConstI8(-4),
            Instruction::Mul(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -52);

        program.instructions = vec![
            Instruction::PushConstI16(-50),
            Instruction::PushConstI16(100),
            Instruction::Mul(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -5000);
    }

    #[test]
    fn div_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(8),
            Instruction::PushConstU8(4),
            Instruction::Div(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 2);

        program.instructions = vec![
            Instruction::PushConstU16(1500),
            Instruction::PushConstU16(500),
            Instruction::Div(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 3);

        program.instructions = vec![
            Instruction::PushConstI8(13),
            Instruction::PushConstI8(-4),
            Instruction::Div(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -3);

        program.instructions = vec![
            Instruction::PushConstI16(1000),
            Instruction::PushConstI16(-50),
            Instruction::Div(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -20);
    }

    #[test]
    fn shr_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(8),
            Instruction::PushConstU8(3),
            Instruction::Shr(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 1);

        program.instructions = vec![
            Instruction::PushConstU16(16),
            Instruction::PushConstU16(1),
            Instruction::Shr(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 8);

        program.instructions = vec![
            Instruction::PushConstI8(32),
            Instruction::PushConstI8(2),
            Instruction::Shr(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 8);

        program.instructions = vec![
            Instruction::PushConstI16(128),
            Instruction::PushConstI16(4),
            Instruction::Shr(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 8);
    }

    #[test]
    fn shl_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(1),
            Instruction::PushConstU8(4),
            Instruction::Shl(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 16);

        program.instructions = vec![
            Instruction::PushConstU16(1),
            Instruction::PushConstU16(8),
            Instruction::Shl(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 256);

        program.instructions = vec![
            Instruction::PushConstI8(1),
            Instruction::PushConstI8(3),
            Instruction::Shl(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 8);

        program.instructions = vec![
            Instruction::PushConstI16(1),
            Instruction::PushConstI16(2),
            Instruction::Shl(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 4);
    }

    #[test]
    fn and_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(0b01010101),
            Instruction::PushConstU8(0xFF),
            Instruction::And(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0b01010101);

        program.instructions = vec![
            Instruction::PushConstU16(0b1010101010101010),
            Instruction::PushConstU16(0xFFFF),
            Instruction::And(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0b1010101010101010);

        program.instructions = vec![
            Instruction::PushConstI8(0b0101),
            Instruction::PushConstI8(0x0F),
            Instruction::And(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 0b0101);

        program.instructions = vec![
            Instruction::PushConstI16(0b01010101),
            Instruction::PushConstI16(0xFF),
            Instruction::And(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0b01010101);
    }

    #[test]
    fn or_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(0xFF),
            Instruction::PushConstU8(0x00),
            Instruction::Or(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0xFF);

        program.instructions = vec![
            Instruction::PushConstU16(0xFF00),
            Instruction::PushConstU16(0x00FF),
            Instruction::Or(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0xFFFF);

        program.instructions = vec![
            Instruction::PushConstI8(0x0F),
            Instruction::PushConstI8(0x00),
            Instruction::Or(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 0x0F);

        program.instructions = vec![
            Instruction::PushConstI16(0x00FF),
            Instruction::PushConstI16(0x0000),
            Instruction::Or(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0x00FF);
    }

    #[test]
    fn xor_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(0xFF),
            Instruction::PushConstU8(0x00),
            Instruction::Xor(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0xFF);

        program.instructions = vec![
            Instruction::PushConstU16(0xFF00),
            Instruction::PushConstU16(0x00FF),
            Instruction::Xor(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0xFFFF);

        program.instructions = vec![
            Instruction::PushConstI8(0x0F),
            Instruction::PushConstI8(0x00),
            Instruction::Xor(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 0x0F);

        program.instructions = vec![
            Instruction::PushConstI16(0x00FF),
            Instruction::PushConstI16(0x0000),
            Instruction::Xor(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0x00FF);
    }

    #[test]
    fn not_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(0x0F),
            Instruction::Not(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0xF0);

        program.instructions = vec![
            Instruction::PushConstU16(0xFF00),
            Instruction::Not(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0x00FF);

        program.instructions = vec![
            Instruction::PushConstI8(0x0F),
            Instruction::Not(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 0xF0);

        program.instructions = vec![
            Instruction::PushConstI16(0x00FF),
            Instruction::Not(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u16().unwrap(), 0xFF00);
    }

    #[test]
    fn neg_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstI8(104),
            Instruction::Neg(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -104);

        program.instructions = vec![
            Instruction::PushConstI16(-1234),
            Instruction::Neg(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 1234);

        program.instructions = vec![Instruction::Neg(IntegerType::U8)];

        assert!(vm.exec(&program, &mut system).is_err());

        program.instructions = vec![Instruction::Neg(IntegerType::U16)];

        assert!(vm.exec(&program, &mut system).is_err());
    }

    #[test]
    fn cmp_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(104),
            Instruction::PushConstU8(98),
            Instruction::Cmp(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.cmp_res, 6);
        assert_eq!(vm.pop_u8().unwrap(), 98);
        assert_eq!(vm.pop_u8().unwrap(), 104);

        program.instructions = vec![
            Instruction::PushConstU16(20000),
            Instruction::PushConstU16(20000),
            Instruction::Cmp(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.cmp_res, 0);
        assert_eq!(vm.pop_u16().unwrap(), 20000);
        assert_eq!(vm.pop_u16().unwrap(), 20000);

        program.instructions = vec![
            Instruction::PushConstI8(-32),
            Instruction::PushConstI8(-64),
            Instruction::Cmp(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.cmp_res, 32);
        assert_eq!(vm.pop_i8().unwrap(), -64);
        assert_eq!(vm.pop_i8().unwrap(), -32);

        program.instructions = vec![
            Instruction::PushConstI16(-3200),
            Instruction::PushConstI16(-6400),
            Instruction::Cmp(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.cmp_res, 3200);
        assert_eq!(vm.pop_i16().unwrap(), -6400);
        assert_eq!(vm.pop_i16().unwrap(), -3200);
    }

    #[test]
    fn inc_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(100),
            Instruction::Inc(IntegerType::U8),
            Instruction::Inc(IntegerType::U8),
            Instruction::Inc(IntegerType::U8),
            Instruction::Inc(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 104);

        program.instructions = vec![
            Instruction::PushConstU16(20000),
            Instruction::Inc(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
            Instruction::Inc(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

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

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -16);

        program.instructions = vec![
            Instruction::PushConstI16(-4),
            Instruction::Inc(IntegerType::I16),
            Instruction::Inc(IntegerType::I16),
            Instruction::Inc(IntegerType::I16),
            Instruction::Inc(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0);
    }

    #[test]
    fn dec_instruction() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstU8(100),
            Instruction::Dec(IntegerType::U8),
            Instruction::Dec(IntegerType::U8),
            Instruction::Dec(IntegerType::U8),
            Instruction::Dec(IntegerType::U8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_u8().unwrap(), 96);

        program.instructions = vec![
            Instruction::PushConstU16(20000),
            Instruction::Dec(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
            Instruction::Dec(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();

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

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), 16);

        program.instructions = vec![
            Instruction::PushConstI16(4),
            Instruction::Dec(IntegerType::I16),
            Instruction::Dec(IntegerType::I16),
            Instruction::Dec(IntegerType::I16),
            Instruction::Dec(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), 0);
    }

    #[test]
    fn promotion_demotion() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![Instruction::PushConstU8(90), Instruction::U8Promote];
        vm.exec(&program, &mut system).unwrap();
        assert_eq!(vm.pop_u16().unwrap(), 90);

        program.instructions = vec![Instruction::PushConstU16(190), Instruction::U16Demote];
        vm.exec(&program, &mut system).unwrap();
        assert_eq!(vm.pop_u8().unwrap(), 190);

        program.instructions = vec![Instruction::PushConstI8(-90), Instruction::I8Promote];
        vm.exec(&program, &mut system).unwrap();
        assert_eq!(vm.pop_i16().unwrap(), -90);

        program.instructions = vec![Instruction::PushConstI16(-120), Instruction::I16Demote];
        vm.exec(&program, &mut system).unwrap();
        assert_eq!(vm.pop_i8().unwrap(), -120);
    }

    #[test]
    fn jumps() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::Jmp(true, 6),
            Instruction::Jp(true, 1),
            Instruction::Jn(true, 1),
            Instruction::Jz(true, 1),
            Instruction::Jnz(true, 1),
            Instruction::Jmp(true, 2),
            Instruction::Jmp(false, 5),
        ];

        vm.exec(&program, &mut system).unwrap();

        program.instructions = vec![
            Instruction::Jmp(true, 1),
            Instruction::PushConstU8(2),
            Instruction::PushConstU8(1),
            Instruction::Cmp(IntegerType::U8),
            Instruction::Jp(true, 100),
        ];
        vm.exec(&program, &mut system).unwrap();

        program.instructions = vec![
            Instruction::Jmp(true, 1),
            Instruction::PushConstI8(1),
            Instruction::PushConstI8(2),
            Instruction::Cmp(IntegerType::I8),
            Instruction::Jn(true, 100),
        ];
        vm.exec(&program, &mut system).unwrap();

        program.instructions = vec![
            Instruction::Jmp(true, 1),
            Instruction::PushConstU8(2),
            Instruction::PushConstU8(2),
            Instruction::Cmp(IntegerType::U8),
            Instruction::Jz(true, 100),
        ];
        vm.exec(&program, &mut system).unwrap();

        program.instructions = vec![
            Instruction::Jmp(true, 1),
            Instruction::PushConstU8(40),
            Instruction::PushConstU8(20),
            Instruction::Cmp(IntegerType::U8),
            Instruction::Jnz(true, 100),
        ];
        vm.exec(&program, &mut system).unwrap();
    }

    #[test]
    fn indirect_addr() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
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

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -1234);
    }

    #[test]
    fn dup_drop() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::PushConstI16(-1234),
            Instruction::PushConstU16(0x0FFF),
            Instruction::PushConstI8(-3),
            Instruction::Drop(IntegerType::I8),
            Instruction::Drop(IntegerType::U16),
            Instruction::Dup(IntegerType::I16),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i16().unwrap(), -1234);
        assert_eq!(vm.pop_i16().unwrap(), -1234);

        program.instructions = vec![
            Instruction::PushConstI8(-120),
            Instruction::PushConstU8(0xFF),
            Instruction::PushConstI16(-2000),
            Instruction::Drop(IntegerType::I16),
            Instruction::Drop(IntegerType::U8),
            Instruction::Dup(IntegerType::I8),
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.pop_i8().unwrap(), -120);
        assert_eq!(vm.pop_i8().unwrap(), -120);
    }

    #[test]
    fn missing_call_for_ret() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![Instruction::Ret];

        let err = vm.exec(&program, &mut system).err().unwrap();
        let formatted_err = format!("{}", err);

        assert_eq!(formatted_err, "cannot return from an empty call stack");
    }

    #[test]
    fn regular_call() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();

        program.instructions = vec![
            Instruction::Call(0x0002),
            Instruction::SysCall(0),
            Instruction::PushConstI16(1234),
            Instruction::PushConstI16(1234),
            Instruction::Sub(IntegerType::I16),
            Instruction::Store(IntegerType::I16, 0x0000),
            Instruction::Ret,
        ];

        vm.exec(&program, &mut system).unwrap();
    }

    #[test]
    #[should_panic]
    fn pop_empty_stack() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();
        program.instructions = vec![Instruction::Drop(IntegerType::U8)];

        vm.exec(&program, &mut system).unwrap();
    }

    #[test]
    #[should_panic]
    fn pop_corrupted_stack() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();
        program.instructions = vec![
            Instruction::PushConstU16(0xAABB),
            Instruction::Drop(IntegerType::U8),
            Instruction::Drop(IntegerType::U16),
        ];

        vm.exec(&program, &mut system).unwrap();
    }

    #[test]
    fn alloc_and_free() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();
        program.instructions = vec![
            Instruction::Alloc(10),
            Instruction::Alloc(30),
            Instruction::Free,
            Instruction::Free,
            Instruction::Alloc(20),
            Instruction::Free,
        ];

        vm.exec(&program, &mut system).unwrap();

        assert_eq!(vm.bp, 0);
    }

    #[test]
    #[should_panic]
    fn heap_crash() {
        let mut vm = VM::default();
        let mut system = helper::generate_system();
        let mut program = helper::generate_program();
        program.mem_pages = Some(1);
        program.instructions = vec![
            Instruction::Alloc(600),
            Instruction::PushConstU16(0xFFFF),
            Instruction::Jmp(false, 1),
        ];

        vm.exec(&program, &mut system).unwrap();
    }
}
