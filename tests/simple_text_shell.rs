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

use melon::{Program, Shell, VM};

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
            mem_size: Some(20),
        },
        &mut TextConsole::new(),
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
            mem_size: Some(20),
        },
        &mut TextConsole::new(),
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
            mem_size: Some(20),
        },
        &mut TextConsole::new(),
    ).unwrap();
}