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

use std::io::{Read, Write};
use std::fs::File;
use std::path::Path;
use instruction::Instruction;
use typedef::*;
use serde::{Deserialize, Serialize};
use rmps::{Deserializer, Serializer};

/// The container for a program
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Program {
    /// The version of the VM API
    pub core_version: String,
    /// The ID of the System the program is compiled against
    pub system_id: String,
    /// The instuctions of the program
    pub instructions: Vec<Instruction>,
    /// (Optional) The number of allocated memory pages (1 page = 1024 Byte)
    pub mem_pages: Option<Address>,
}

impl Program {
    /// Loads a MsgPack encoded melon image from the given file
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Program> {
        let mut file = File::open(path)?;

        let mut buf = Vec::new();
        file.read_to_end(&mut buf)?;
        let mut de = Deserializer::new(&buf[..]);

        let res = Deserialize::deserialize(&mut de)?;

        Ok(res)
    }

    /// Saves the program to the given MsgPack encoded image file
    pub fn save_as<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut buf = Vec::new();
        self.serialize(&mut Serializer::new(&mut buf))?;

        let mut file = File::create(path)?;
        file.write_all(&buf[..])?;
        file.flush()?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn save_and_load() {
        const FILE_NAME: &str = "test.img";

        let program = Program {
            core_version: "bogus_version".into(),
            system_id: "bogus_system".into(),
            instructions: Default::default(),
            mem_pages: Some(1),
        };

        program.save_as(FILE_NAME).unwrap();

        let loaded_program = Program::from_file(FILE_NAME).unwrap();

        fs::remove_file(FILE_NAME).unwrap();

        assert_eq!(program.core_version, loaded_program.core_version);
        assert_eq!(program.system_id, loaded_program.system_id);
        assert_eq!(program.mem_pages, loaded_program.mem_pages);
    }
}
