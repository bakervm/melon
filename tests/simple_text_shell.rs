

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
    const ID: &'static str = "com.example.text-console";

    const MEM_PAGES: u8 = 1;
}

#[test]
fn create() {
    let mut virt = VM::default();
    virt.exec(
        &ProgramBuilder::new(TextConsole::ID).mem_pages(20).gen(),
        &mut TextConsole::new(),
    )
    .unwrap();
}

#[test]
fn wrong_system_id() {
    let mut virt = VM::default();

    virt.exec(
        &ProgramBuilder::new("com.example.pixel-display")
            .mem_pages(20)
            .gen(),
        &mut TextConsole::new(),
    )
    .unwrap_err();
}
