use instruction::Instruction;

pub struct Program {
    pub core_version: String,
    pub shell_id: String,
    pub instructions: Vec<Instruction>,
}
