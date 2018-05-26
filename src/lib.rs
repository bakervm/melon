#![deny(missing_docs)]

//! A library for creating retro computing platforms
//!
//! # Introduction
//! `melon` is like a virtual 16bit CPU. When building a retro computing platform e.g. a gaming
//! console or old computer architecture, `melon` takes care of handling basic parts like stack
//! management, calls, memory management and exception handling. Its most common interface, the
//! [System][system] trait makes it possible to not only implement the CPU into any platform but
//! makes it also really easy to extend its functionality.
//!
//! The [Program][program] struct takes care of loading and saving programs written for an
//! implementation of the `melon` backend. `melon` roms are gzipped msgpack files.
//!
//! [system]: trait.System.html
//! [program]: struct.Program.html

extern crate byteorder;
#[macro_use]
extern crate failure;
extern crate rand;
#[macro_use]
extern crate rand_derive;
extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate flate2;
extern crate rmp_serde as rmps;
extern crate rustyline;

mod debugger;
mod instruction;
mod program;
mod system;
pub mod typedef;
mod vm;

pub use debugger::*;
pub use instruction::*;
pub use program::*;
pub use system::*;
pub use vm::*;
