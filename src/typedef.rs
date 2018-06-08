//! A couple of useful type aliases

/// A memory or instruction address
pub type Address = u16;

/// A handy alias for `Result` that carries a generic error type.
pub type Result<T> = ::std::result::Result<T, ::failure::Error>;

/// The file extension of melon roms
pub const ROM_FILE_EXTENSION: &str = "rom";

#[derive(Fail, Debug)]
#[allow(missing_docs)]
pub enum VMError {
    #[fail(display = "wrong system ID. Runtime: {:?} Program: {:?}", runtime, program)]
    WrongSystemId { program: String, runtime: String },
    #[fail(display = "wrong target version. Runtime: {:?} Program: {:?}", runtime, program)]
    WrongTargetVersion { program: String, runtime: String },
    #[fail(
        display = "requested memory too big. Requested pages: {}. Maximum number of pages: {}",
        requested,
        max
    )]
    RequestedMemoryTooBig { requested: u8, max: u8 },
    #[fail(display = "requested memory too small. Number of memory pages has to be at least one")]
    RequestedMemoryTooSmall,
    #[fail(display = "program has too many instructions. Maximum number of instructions: {}", max)]
    TooManyInstructions { max: u16 },
    #[fail(display = "entry point does not point to a valid instruction")]
    InvalidEntryPoint,
    #[fail(display = "could no find instruction at %{:04X}", pc)]
    InvalidProgramCounter { pc: u16 },
    #[fail(display = "memory address ${:04X} out of bounds", addr)]
    InvalidMemoryAddress { addr: u16 },
    #[fail(display = "heap crash detected! Heap cannot overlap with stack")]
    HeapCrash,
    #[fail(display = "cannot pop a value off an empty stack")]
    PopEmptyStack,
    #[fail(display = "attempt to {} with overflow", op)]
    ArithmeticOverflow { op: String },
    #[fail(display = "attempt to divide by zero")]
    DivideByZero,
    #[fail(
        display = "unable to apply the \"{}\" instruction to values larger than or equal to the number of bits",
        instr
    )]
    UnableToApplyInstruction { instr: String },
    #[fail(display = "cannot create negative unsigned value")]
    NegativeUnsigned,
    #[fail(display = "cannot return from an empty call stack")]
    ReturnFromEmptyCallStack,
    #[fail(display = "cannot free unallocated memory")]
    FreeUnallocatedMemory,
    #[fail(display = "jump resulted in an unwanted hang of the program")]
    JumpResultedInUnwantedHang,
    #[fail(display = "call resulted in an unwanted hang of the program")]
    CallResultedInUnwantedHang,
}
