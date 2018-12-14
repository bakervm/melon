use crate::consts;
use crate::instruction::Instruction;
use crate::typedef::*;
use flate2::{read::GzDecoder, write::GzEncoder, Compression};
use rmp_serde::{Deserializer, Serializer};
use semver::Version;
use serde::{Deserialize, Serialize};
use std::{
    fs::File,
    io::{Read, Write},
    path::Path,
};

/// The container for a program
///
/// You can load a `Program` from a file or create one using the [ProgramBuilder][program_builder]
///
/// [program_builder]: struct.ProgramBuilder.html
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Program {
    /// The target version of the `melon` API the program was compiled against
    target_version: Version,
    /// The ID of the System the program is compiled against
    system_id: String,
    /// The instuctions of the program
    instructions: Vec<Instruction>,
    /// (Optional) The *minimum* number of allocated memory pages (1 page = 1024 Byte)
    mem_pages: Option<u8>,
    /// The entry address of the program
    entry_point: Address,
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

    /// The target version of the `melon` API the program was compiled against
    pub fn target_version(&self) -> &Version {
        &self.target_version
    }
    /// The ID of the System the program is compiled against
    pub fn system_id(&self) -> &String {
        &self.system_id
    }
    /// The instuctions of the program
    pub fn instructions(&self) -> &Vec<Instruction> {
        &self.instructions
    }
    /// (Optional) The *minimum* number of allocated memory pages (1 page = 1024 Byte)
    pub fn mem_pages(&self) -> Option<u8> {
        self.mem_pages
    }
    /// The entry address of the program
    pub fn entry_point(&self) -> Address {
        self.entry_point
    }
}

/// A builder for generating `Program`s
pub struct ProgramBuilder {
    /// The ID of the System the program is compiled against
    system_id: String,
    /// The instuctions of the program
    instructions: Vec<Instruction>,
    /// (Optional) The *minimum* number of allocated memory pages (1 page = 1024 Byte)
    mem_pages: Option<u8>,
    /// The entry address of the program
    entry_point: Address,
}

impl ProgramBuilder {
    /// Creates a new `ProgramBuilder` with the given system_id
    pub fn new(system_id: &str) -> ProgramBuilder {
        ProgramBuilder {
            system_id: system_id.into(),
            entry_point: 0,
            instructions: Vec::new(),
            mem_pages: None,
        }
    }

    /// Adds instructions to the builder
    pub fn instructions(mut self, instructions: Vec<Instruction>) -> ProgramBuilder {
        self.instructions = instructions;
        self
    }

    /// Adds an entry point to the builder
    pub fn entry_point(mut self, entry_point: Address) -> ProgramBuilder {
        self.entry_point = entry_point;
        self
    }

    /// Adds a requirement for memory pages to the builder
    pub fn mem_pages(mut self, mem_pages: u8) -> ProgramBuilder {
        self.mem_pages = Some(mem_pages);
        self
    }

    /// Generates a `Program` with the given setup and also overwrites the version number
    #[cfg(test)]
    pub(crate) fn gen_with_version(&self, version: &str) -> Program {
        Program {
            target_version: Version::parse(version).expect("unable to parse version"),
            system_id: self.system_id.clone(),
            instructions: self.instructions.clone(),
            mem_pages: self.mem_pages,
            entry_point: self.entry_point,
        }
    }

    /// Generates a `Program` with the given setup
    pub fn gen(&self) -> Program {
        Program {
            target_version: (*consts::VERSION).clone(),
            system_id: self.system_id.clone(),
            instructions: self.instructions.clone(),
            mem_pages: self.mem_pages,
            entry_point: self.entry_point,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{distributions::Standard, thread_rng, Rng};
    use std::path::PathBuf;
    use tempfile::TempDir;

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

        let program = ProgramBuilder::new("bogus_system")
            .mem_pages(1)
            .instructions(rng.sample_iter(&Standard).take(100).collect())
            .gen_with_version("0.0.0");

        program.save_as(&file_name).unwrap();

        let loaded_program = Program::from_file(&file_name).unwrap();

        assert_eq!(program.target_version, loaded_program.target_version);
        assert_eq!(program.system_id, loaded_program.system_id);
        assert_eq!(program.mem_pages, loaded_program.mem_pages);
    }
}
