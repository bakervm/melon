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

#![allow(missing_docs)]

use typedef::*;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum Instruction {
    Add(IntegerType),
    Sub(IntegerType),
    Mul(IntegerType),
    Div(IntegerType),
    Sar(IntegerType),
    Sal(IntegerType),
    Neg(IntegerType),
    Shr(IntegerType),
    Shl(IntegerType),
    And(IntegerType),
    Or(IntegerType),
    Xor(IntegerType),
    Not(IntegerType),
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

    /// Loads a u16 from the given register and pushes it onto the stack
    LoadReg(Register),

    /// Loads a value from the given address and pushes it onto the stack
    Load(IntegerType, Address),

    /// Pops the top value off the stack and stores it at the given address
    Store(IntegerType, Address),

    Dup(IntegerType),
    Drop(IntegerType),

    Int(UInt),

    Call(Address),
    Ret,

    Jmp(Int),
    Jnz(Int),
    Jz(Int),
    Jn(Int),
    Jp(Int),
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum IntegerType {
    U8,
    U16,
    I8,
    I16,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
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
