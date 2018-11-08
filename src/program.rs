use flate2::{read::GzDecoder, write::GzEncoder, Compression};
use instruction::Instruction;
use rmps::{Deserializer, Serializer};
use serde::{Deserialize, Serialize};
use std::{
    fs::File,
    io::{Read, Write},
    path::Path,
};
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

        let res = Self::from_slice(&gz_buf)?;

        Ok(res)
    }

    /// Decodes a program from MsgPack encoded and gzipped image data
    pub fn from_slice(vec: &[u8]) -> Result<Program> {
        let mut decoder = GzDecoder::new(&vec[..]);
        let mut msgpack_buf = Vec::new();
        decoder.read_to_end(&mut msgpack_buf)?;

        let mut de = Deserializer::new(&msgpack_buf[..]);

        let res = Deserialize::deserialize(&mut de)?;

        Ok(res)
    }

    /// Encodes the program as MsgPack encoded and gzipped image data
    pub fn to_vec(&self) -> Result<Vec<u8>> {
        let mut msgpack_buf = Vec::new();
        self.serialize(&mut Serializer::new(&mut msgpack_buf))?;

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&msgpack_buf[..])?;
        let gz_buf = encoder.finish()?;

        Ok(gz_buf)
    }

    /// Saves the program as a MsgPack encoded and gzipped image to the given file
    pub fn save_as<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let gz_buf = self.to_vec()?;

        let mut file = File::create(path)?;
        file.write_all(&gz_buf[..])?;
        file.flush()?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    extern crate tempfile;

    use self::tempfile::TempDir;
    use super::*;
    use rand::{distributions::Standard, thread_rng, Rng};
    use std::path::PathBuf;

    fn gen_dir() -> TempDir {
        tempfile::tempdir().expect("unable to create temporary directory")
    }

    #[test]
    fn save_and_load() {
        let mut rng = thread_rng();
        let tmp_dir = gen_dir();

        let file_name = tmp_dir
            .path()
            .join(PathBuf::from("test").with_extension(ROM_FILE_EXTENSION));

        let program = Program {
            target_version: "bogus_version".into(),
            system_id: "bogus_system".into(),
            instructions: rng.sample_iter(&Standard).take(100).collect(),
            mem_pages: Some(1),
            entry_point: 0,
        };

        program.save_as(&file_name).unwrap();

        let loaded_program = Program::from_file(&file_name).unwrap();

        assert_eq!(program.target_version, loaded_program.target_version);
        assert_eq!(program.system_id, loaded_program.system_id);
        assert_eq!(program.mem_pages, loaded_program.mem_pages);
    }
}
