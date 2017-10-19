extern crate serde;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate error_chain;

#[macro_use]
pub mod errors;
pub mod instruction;
pub mod typedef;
pub mod vm;
pub mod program;
pub mod shell;
