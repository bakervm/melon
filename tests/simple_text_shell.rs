extern crate melon;

use melon::shell::Shell;
use melon::program::Program;
use melon::vm::VM;

struct TextConsole;

impl Shell for TextConsole {
    const ID: &'static str = "__TEXT_CONSOLE__";
}

#[test]
fn create() {
    let mut virt = VM::default();
    virt.exec(
        Program {
            core_version: env!("CARGO_PKG_VERSION").into(),
            shell_id: TextConsole::ID.into(),
            instructions: Vec::new(),
        },
        &mut TextConsole,
    ).unwrap();
}

#[test]
#[should_panic]
fn wrong_shell_id() {
    let mut virt = VM::default();

    virt.exec(
        Program {
            core_version: env!("CARGO_PKG_VERSION").into(),
            shell_id: "__PIXEL_DISPLAY__".into(),
            instructions: Vec::new(),
        },
        &mut TextConsole,
    ).unwrap();
}

#[test]
#[should_panic]
fn wrong_core_version() {
    let mut virt = VM::default();

    virt.exec(
        Program {
            core_version: "0.0.0".into(),
            shell_id: TextConsole::ID.into(),
            instructions: Vec::new(),
        },
        &mut TextConsole,
    ).unwrap();
}
