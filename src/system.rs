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

use vm::VM;
use typedef::*;

#[allow(unused_variables)]
/// An interface to communicate with the VM
///
/// # Example
///
/// If you wanted to implement a text based system you could write something like this:
///
/// ```
/// use melon::{Shell, VM};
/// use melon::typedef::*;
/// use std::sync::mpsc::Receiver;
///
/// pub const MAX_CHARACTERS_PER_LINE: usize = 100;
///
/// pub struct TextSystem {
///     current_output_line: String,
///     current_input_line: String,
///     recv: Receiver<u8>,
/// }
///
/// impl TextSystem {
///     /// The receiver allows you to safely inject characters from another thread
///     pub fn new(recv: Receiver<u8>) -> TextSystem {
///         TextSystem {
///             current_output_line: Default::default(),
///             current_input_line: Default::default(),
///             recv: recv,
///         }
///     }
/// }
///
/// impl Shell for TextSystem {
///     const ID: &'static str = "__TEXT_SYSTEM__";
///
///     fn int(&mut self, vm: &mut VM, signal: UInt) -> Result<()> {
///         match signal {
///             // This is pretty much like `write_line`
///             1 => {
///                 // Read the memory of the vm until you reach the terminal `0x00` but only to a
///                 // maximum of 100 characters
///                 let line = vm.mem
///                     .iter()
///                     .take(MAX_CHARACTERS_PER_LINE)
///                     .map(|x| *x)
///                     .take_while(|x| x != &0_u8)
///                     .collect::<Vec<u8>>();
///
///                 self.current_output_line = String::from_utf8(line)?;
///
///                 println!("{}", self.current_output_line);
///             }
///             // This is pretty much like `read_line`
///             2 => {
///                 // Receive single characters until you reach the terminal `0x00` but only to a
///                 // maximum of 100 characters
///                 let mut line = self.recv
///                     .iter()
///                     .take(MAX_CHARACTERS_PER_LINE)
///                     .take_while(|x| x != &0_u8)
///                     .collect::<Vec<u8>>();
///
///                 line.push(0); // Push terminal `0x00`
///
///                 self.current_input_line = String::from_utf8(line.clone())?;
///
///                 // Copy characters to vm memory
///                 for i in 0..line.len() {
///                     let vm_index = (MAX_CHARACTERS_PER_LINE + 1) + i;
///                     vm.mem[vm_index] = line[i];
///                 }
///             }
///             _ => unreachable!(),
///         }
///
///         Ok(())
///     }
/// }
/// ```
///
/// Following the basic principles in this example, you are able to build any retro style computing
/// system you want.
///
pub trait System: Send {
    /// A unique ID to identify the System
    const ID: &'static str;

    /// Hook into the state after each cycle
    fn process(&mut self, vm: &mut VM) -> Result<()> {
        Ok(())
    }

    /// Prepare the state of the VM
    fn prepare(&mut self, vm: &mut VM) -> Result<()> {
        Ok(())
    }

    /// Make finalizing manipulations to the state before the VM's shutdown
    fn finish(&mut self, vm: &mut VM) -> Result<()> {
        Ok(())
    }

    /// React to the `SysCall` instruction and process the given signal
    fn system_call(&mut self, vm: &mut VM, signal: UInt) -> Result<()> {
        Ok(())
    }
}
