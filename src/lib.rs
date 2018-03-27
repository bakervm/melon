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

mod instruction;
mod program;
mod system;
pub mod typedef;
mod vm;

pub use instruction::*;
pub use program::*;
pub use system::*;
pub use vm::*;
