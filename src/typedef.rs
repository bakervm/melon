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

//! A couple of useful type aliases

/// An unsigned integer with 8 bit
pub type SmallUInt = u8;
/// An unsigned integer with 16 bit
pub type UInt = u16;

/// An integer with 8 bit
pub type SmallInt = i8;
/// An integer with 16 bit
pub type Int = i16;

/// Typedef of a usize
pub type Address = u16;

/// A handy alias for `Result` that carries a generic error type.
pub type Result<T> = ::std::result::Result<T, ::failure::Error>;
