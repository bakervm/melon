use typedef::*;
use vm::VM;

#[allow(unused_variables)]
/// An interface to communicate with the VM
///
/// # Example
///
/// If you wanted to implement a text based system you could write something like this:
///
/// ```
/// extern crate melon;
///
/// use melon::typedef::*;
/// use melon::{System, VM};
/// use std::sync::mpsc::Receiver;
///
///
/// pub const MAX_CHARACTERS_PER_LINE: usize = 100;
///
/// pub struct TextSystem {
///     current_output_line: String,
///     current_input_line: String,
///     recv: Receiver<u8>,
/// }
///
/// # fn main() {}
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
/// impl System for TextSystem {
///     const ID: &'static str = "__TEXT_SYSTEM__";
///
///     const MEM_PAGES: u8 = 1;
///
///     fn system_call(&mut self, vm: &mut VM, signal: UInt) -> Result<()> {
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

    /// The minimum number of memory pages required for this system
    const MEM_PAGES: u8;

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
