#![allow(missing_docs)]

use crate::typedef::*;
use rand_derive::Rand;

#[derive(Serialize, Deserialize, Copy, Clone, Debug, Rand)]
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

#[derive(Serialize, Deserialize, Copy, Clone, Debug, Rand)]
pub enum IntegerType {
    U8,
    U16,
    I8,
    I16,
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug, Rand)]
pub enum Register {
    StackPtr,
    BasePtr,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn instruction_size() {
        let size = size_of::<Instruction>();

        assert_eq!(size, 4);
    }

    #[test]
    fn register_size() {
        let size = size_of::<Register>();

        assert_eq!(size, 1);
    }

    #[test]
    fn type_size() {
        let size = size_of::<IntegerType>();

        assert_eq!(size, 1);
    }
}
