#![allow(missing_docs)]

use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use crate::typedef::*;

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub enum Instruction {
    Add(IntegerType),
    Sub(IntegerType),
    Mul(IntegerType),
    Div(IntegerType),
    Shr(IntegerType),
    Shl(IntegerType),
    And(IntegerType),
    Or(IntegerType),
    Xor(IntegerType),
    Not(IntegerType),
    Neg(IntegerType),
    Cmp(IntegerType),
    Inc(IntegerType),
    Dec(IntegerType),

    U8Promote,
    U16Demote,
    I8Promote,
    I16Demote,

    PushConstU8(u8),
    PushConstU16(u16),
    PushConstI8(i8),
    PushConstI16(i16),

    LoadReg(Register),

    Load(IntegerType, Address),
    LoadIndirect(IntegerType),
    Store(IntegerType, Address),
    StoreIndirect(IntegerType),

    Dup(IntegerType),
    Drop(IntegerType),

    SysCall(u16),

    Call(Address),
    Ret,

    Alloc(u16),
    Free,

    Jmp(bool, u16),
    Jeq(bool, u16),
    Jneq(bool, u16),
    Jlt(bool, u16),
    JltEq(bool, u16),
    Jgt(bool, u16),
    JgtEq(bool, u16),
}

impl Distribution<Instruction> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Instruction {
        let choice: u8 = rng.gen_range(0, 41);

        match choice {
            0 => Instruction::Add(rng.gen()),
            1 => Instruction::Sub(rng.gen()),
            2 => Instruction::Mul(rng.gen()),
            3 => Instruction::Div(rng.gen()),
            4 => Instruction::Shr(rng.gen()),
            5 => Instruction::Shl(rng.gen()),
            6 => Instruction::And(rng.gen()),
            7 => Instruction::Or(rng.gen()),
            8 => Instruction::Xor(rng.gen()),
            9 => Instruction::Not(rng.gen()),
            10 => Instruction::Neg(rng.gen()),
            11 => Instruction::Cmp(rng.gen()),
            12 => Instruction::Inc(rng.gen()),
            13 => Instruction::Dec(rng.gen()),
            14 => Instruction::U8Promote,
            15 => Instruction::U16Demote,
            16 => Instruction::I8Promote,
            17 => Instruction::I16Demote,
            18 => Instruction::PushConstU8(rng.gen()),
            19 => Instruction::PushConstU16(rng.gen()),
            20 => Instruction::PushConstI8(rng.gen()),
            21 => Instruction::PushConstI16(rng.gen()),
            22 => Instruction::LoadReg(rng.gen()),
            23 => Instruction::Load(rng.gen(), rng.gen()),
            24 => Instruction::LoadIndirect(rng.gen()),
            25 => Instruction::Store(rng.gen(), rng.gen()),
            26 => Instruction::StoreIndirect(rng.gen()),
            27 => Instruction::Dup(rng.gen()),
            28 => Instruction::Drop(rng.gen()),
            29 => Instruction::SysCall(rng.gen()),
            30 => Instruction::Call(rng.gen()),
            31 => Instruction::Ret,
            32 => Instruction::Alloc(rng.gen()),
            33 => Instruction::Free,
            34 => Instruction::Jmp(rng.gen(), rng.gen()),
            35 => Instruction::Jneq(rng.gen(), rng.gen()),
            36 => Instruction::Jeq(rng.gen(), rng.gen()),
            37 => Instruction::Jlt(rng.gen(), rng.gen()),
            38 => Instruction::JltEq(rng.gen(), rng.gen()),
            39 => Instruction::Jgt(rng.gen(), rng.gen()),
            40 => Instruction::JgtEq(rng.gen(), rng.gen()),
            _ => unreachable!(),
        }
    }
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub enum IntegerType {
    U8,
    U16,
    I8,
    I16,
}

impl Distribution<IntegerType> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> IntegerType {
        let choice: u8 = rng.gen_range(0, 4);

        match choice {
            0 => IntegerType::U8,
            1 => IntegerType::U16,
            2 => IntegerType::I8,
            3 => IntegerType::I16,
            _ => unreachable!(),
        }
    }
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub enum Register {
    StackPtr,
    BasePtr,
}

impl Distribution<Register> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Register {
        let choice: u8 = rng.gen_range(0, 2);

        match choice {
            0 => Register::StackPtr,
            1 => Register::BasePtr,
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instruction_size() {
        let size = ::std::mem::size_of::<Instruction>();

        assert_eq!(size, 4);
    }

    #[test]
    fn register_size() {
        let size = ::std::mem::size_of::<Register>();

        assert_eq!(size, 1);
    }

    #[test]
    fn type_size() {
        let size = ::std::mem::size_of::<IntegerType>();

        assert_eq!(size, 1);
    }
}
