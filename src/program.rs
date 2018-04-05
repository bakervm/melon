use flate2::{Compression, read::GzDecoder, write::GzEncoder};
use instruction::Instruction;
use rmps::{Deserializer, Serializer};
use serde::{Deserialize, Serialize};
use std::{fs::File, io::{Read, Write}, path::Path};
use typedef::*;

/// The container for a program
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Program {
    /// The target version of the `melon` API
    pub target_version: String,
    /// The ID of the System the program is compiled against
    pub system_id: String,
    /// The instuctions of the program
    pub instructions: Vec<Instruction>,
    /// (Optional) The *minimum* number of allocated memory pages (1 page = 1024 Byte)
    pub mem_pages: Option<u8>,
    /// The entry address of the program
    pub entry_point: Address,
}

impl Program {
    /// Loads a MsgPack encoded and gzipped melon image from the given file
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Program> {
        let mut file = File::open(path)?;

        let mut gz_buf = Vec::new();
        file.read_to_end(&mut gz_buf)?;

        let mut decoder = GzDecoder::new(&gz_buf[..]);
        let mut msgpack_buf = Vec::new();
        decoder.read_to_end(&mut msgpack_buf)?;

        let mut de = Deserializer::new(&msgpack_buf[..]);

        let res = Deserialize::deserialize(&mut de)?;

        Ok(res)
    }

    /// Saves the program as a MsgPack encoded and gzipped image to the given file
    pub fn save_as<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut msgpack_buf = Vec::new();
        self.serialize(&mut Serializer::new(&mut msgpack_buf))?;

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&msgpack_buf[..])?;
        let gz_buf = encoder.finish()?;

        let mut file = File::create(path)?;
        file.write_all(&gz_buf[..])?;
        file.flush()?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{self, Rng};
    use std::fs;

    #[test]
    fn save_and_load() {
        let mut rng = rand::thread_rng();

        let file_name = format!("test.{}", ROM_FILE_EXTENSION);

        let program = Program {
            target_version: "bogus_version".into(),
            system_id: "bogus_system".into(),
            instructions: rng.gen_iter().take(100).collect(),
            mem_pages: Some(1),
            entry_point: 0,
        };

        program.save_as(file_name.clone()).unwrap();

        let loaded_program = Program::from_file(file_name.clone()).unwrap();

        fs::remove_file(file_name.clone()).unwrap();

        assert_eq!(program.target_version, loaded_program.target_version);
        assert_eq!(program.system_id, loaded_program.system_id);
        assert_eq!(program.mem_pages, loaded_program.mem_pages);
    }
}
