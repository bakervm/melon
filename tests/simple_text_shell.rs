extern crate melon;

use melon::{ProgramBuilder, System, VM};

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
        &ProgramBuilder::new(TextConsole::ID.into())
            .mem_pages(20)
            .gen(),
        &mut TextConsole::new(),
    ).unwrap();
}

#[test]
fn wrong_system_id() {
    let mut virt = VM::default();

    virt.exec(
        &ProgramBuilder::new("__PIXEL_DISPLAY__".into())
            .mem_pages(20)
            .gen(),
        &mut TextConsole::new(),
    ).unwrap_err();
}
