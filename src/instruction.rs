#![allow(missing_docs)]

use typedef::*;

#[derive(Serialize, Deserialize, Clone, Debug, Rand)]
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

    PushConstU8(SmallUInt),
    PushConstU16(UInt),
    PushConstI8(SmallInt),
    PushConstI16(Int),

    LoadReg(Register),

    Load(IntegerType, Address),
    LoadIndirect(IntegerType),
    Store(IntegerType, Address),
    StoreIndirect(IntegerType),

    Dup(IntegerType),
    Drop(IntegerType),

    SysCall(UInt),

    Call(Address),
    Ret,

    Alloc(UInt),
    Free,

    Jmp(bool, UInt),
    Jeq(bool, UInt),
    Jneq(bool, UInt),
    Jlt(bool, UInt),
    JltEq(bool, UInt),
    Jgt(bool, UInt),
    JgtEq(bool, UInt),
}

#[derive(Serialize, Deserialize, Clone, Debug, Rand)]
pub enum IntegerType {
    U8,
    U16,
    I8,
    I16,
}

#[derive(Serialize, Deserialize, Clone, Debug, Rand)]
pub enum Register {
    StackPtr,
    BasePtr,
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
