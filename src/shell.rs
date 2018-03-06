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
pub trait Shell: Send {
    /// A unique ID to identify the Shell
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

    /// React to the `Int` instruction and process the given signal
    fn int(&mut self, vm: &mut VM, signal: Address) -> Result<()> {
        Ok(())
    }
}
