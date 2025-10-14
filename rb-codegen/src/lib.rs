use smallvec::SmallVec;

pub struct Function {
  pub args:   u32,
  pub rets:   u32,
  pub blocks: Vec<Block>,
}

pub struct BlockId(u32);
pub struct Variable(u32);

pub struct Block {
  pub instructions: Vec<Instruction>,
  pub terminator:   TerminatorInstruction,
}

pub struct Instruction {
  pub opcode: Opcode,
  pub input:  SmallVec<[InstructionInput; 2]>,
  pub output: SmallVec<[InstructionOutput; 2]>,
}

pub enum TerminatorInstruction {
  Jump(BlockId),
  Return,
  Trap,
}

pub enum Opcode {
  Add,
  Move,
  Branch(Condition, BlockId),
  Syscall,
}

pub enum Condition {
  Equal,
  NotEqual,
  Greater,
  Less,
  GreaterEqual,
  LessEqual,
}

pub enum InstructionInput {
  Var(Variable),
  Imm(u32),
}

pub enum InstructionOutput {
  Var(Variable),
  Syscall,
}

impl BlockId {
  pub const fn new(id: u32) -> Self { BlockId(id) }

  pub const fn as_u32(&self) -> u32 { self.0 }
}
impl Variable {
  pub const fn new(id: u32) -> Self { Variable(id) }

  pub const fn as_u32(&self) -> u32 { self.0 }
}
