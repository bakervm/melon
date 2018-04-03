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
        },
        &mut TextConsole::new(),
    ).unwrap();
}
