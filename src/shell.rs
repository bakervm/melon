use vm::VM;
use errors::*;

pub trait Shell {
    /// A unique ID to identify the Shell
    const ID: &'static str;

    /// Manipulate the state after a cycle is completed
    fn process(&mut self, _vm: &mut VM) -> Result<()> {
        Ok(())
    }

    /// Prepare the state of the VM
    fn prepare(&mut self, _vm: &mut VM) -> Result<()> {
        Ok(())
    }

    /// Make finalizing manipulations to the state before the VM's shutdown
    fn finish(&mut self, _vm: &mut VM) -> Result<()> {
        Ok(())
    }

    /// React to the `Flush` instruction
    fn flush(&mut self, _vm: &mut VM) -> Result<()> {
        Ok(())
    }
}
