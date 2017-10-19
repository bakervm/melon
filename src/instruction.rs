use typedef::*;

#[derive(Serialize, Deserialize, Clone)]
pub enum Instruction {
    IAdd(Argument, Argument),
    UAdd(Argument, Argument),
    FAdd(Argument, Argument),

    ISub(Argument, Argument),
    USub(Argument, Argument),
    FSub(Argument, Argument),

    IMul(Argument, Argument),
    UMul(Argument, Argument),
    FMul(Argument, Argument),

    IDiv(Argument, Argument),
    UDiv(Argument, Argument),
    FDiv(Argument, Argument),

    Shr(Argument, Argument),
    Shl(Argument, Argument),

    Sar(Argument, Argument),
    Sal(Argument, Argument),

    Push(Argument),
    Pop(Argument),

    Mov(Argument, Argument),

    Flush,

    Jmp(Argument),
    WJmp(Argument),
}

#[derive(Serialize, Deserialize, Clone)]
pub enum Argument {
    Const(Value),
    Pointer(Address),
}
