use smallvec::SmallVec;

pub struct Function {
  pub args:   u32,
  pub rets:   u32,
  pub blocks: Vec<Block>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockId(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Variable(u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
  pub instructions: Vec<Instruction>,
  pub terminator:   TerminatorInstruction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
  pub opcode: Opcode,
  pub input:  SmallVec<[InstructionInput; 2]>,
  pub output: SmallVec<[InstructionOutput; 2]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TerminatorInstruction {
  Jump(BlockId),
  Return,
  Trap,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Opcode {
  Add,
  Lea(Symbol),
  Move,
  Branch(Condition, BlockId),
  Syscall,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Condition {
  Equal,
  NotEqual,
  Greater,
  Less,
  GreaterEqual,
  LessEqual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionInput {
  Var(Variable),
  Imm(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionOutput {
  Var(Variable),
  Syscall,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Symbol {
  pub index: u32,
}

impl BlockId {
  pub const fn new(id: u32) -> Self { BlockId(id) }

  pub const fn as_u32(&self) -> u32 { self.0 }
}
impl Variable {
  pub const fn new(id: u32) -> Self { Variable(id) }

  pub const fn as_u32(&self) -> u32 { self.0 }
}

impl From<Variable> for InstructionInput {
  fn from(v: Variable) -> Self { InstructionInput::Var(v) }
}
impl From<u32> for InstructionInput {
  fn from(v: u32) -> Self { InstructionInput::Imm(v) }
}
impl From<Variable> for InstructionOutput {
  fn from(v: Variable) -> Self { InstructionOutput::Var(v) }
}
