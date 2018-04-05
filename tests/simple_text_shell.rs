extern crate melon;

use melon::{Program, System, VM};

struct TextConsole {
    _current_line: String,
}

impl TextConsole {
    pub fn new() -> TextConsole {
        TextConsole {
            _current_line: String::new(),
        }
    }
}

impl System for TextConsole {
    const ID: &'static str = "__TEXT_CONSOLE__";

    const MEM_PAGES: u8 = 1;
}

#[test]
fn create() {
    let mut virt = VM::default();
    virt.exec(
        &Program {
            target_version: env!("CARGO_PKG_VERSION").into(),
            system_id: TextConsole::ID.into(),
            instructions: Vec::new(),
            mem_pages: Some(20),
            entry_point: 0,
        },
        &mut TextConsole::new(),
    ).unwrap();
}

#[test]
#[should_panic]
fn wrong_system_id() {
    let mut virt = VM::default();

    virt.exec(
        &Program {
            target_version: env!("CARGO_PKG_VERSION").into(),
            system_id: "__PIXEL_DISPLAY__".into(),
            instructions: Vec::new(),
            mem_pages: Some(20),
            entry_point: 0,
        },
        &mut TextConsole::new(),
    ).unwrap();
}

#[test]
#[should_panic]
fn wrong_target_version() {
    let mut virt = VM::default();

    virt.exec(
        &Program {
            target_version: "0.0.0".into(),
            system_id: TextConsole::ID.into(),
            instructions: Vec::new(),
            mem_pages: Some(20),
            entry_point: 0,
        },
        &mut TextConsole::new(),
    ).unwrap();
}
