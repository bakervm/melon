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

//! A library for creating retro computing platforms.
//!
//! # Introduction
//! When creating a virtual machine you first have to think about the usecase. Where does the VM
//! run, when does it run and who is operating it? With **melon**, you *don't* have to think about
//! anything else.

extern crate byteorder;
#[macro_use]
extern crate failure;
extern crate serde;
#[macro_use]
extern crate serde_derive;

mod instruction;
pub mod typedef;
mod vm;
mod program;
mod shell;

pub use instruction::*;
pub use vm::*;
pub use program::*;
pub use shell::*;
