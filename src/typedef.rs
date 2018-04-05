//! A couple of useful type aliases

/// An unsigned integer with 8 bit
pub type SmallUInt = u8;
/// An unsigned integer with 16 bit
pub type UInt = u16;

/// An integer with 8 bit
pub type SmallInt = i8;
/// An integer with 16 bit
pub type Int = i16;

/// A memory or instruction address
pub type Address = u16;

/// A handy alias for `Result` that carries a generic error type.
pub type Result<T> = ::std::result::Result<T, ::failure::Error>;

/// The file extension of melon roms
pub const ROM_FILE_EXTENSION: &str = "rom";
