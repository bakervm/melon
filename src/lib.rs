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

#[macro_use]
extern crate failure;

mod consts;
mod debugger;
mod instruction;
mod program;
mod system;
pub mod typedef;
mod vm;

pub use crate::debugger::*;
pub use crate::instruction::*;
pub use crate::program::*;
pub use crate::system::*;
pub use crate::vm::*;
