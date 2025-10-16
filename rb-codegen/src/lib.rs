use std::fmt;

use smallvec::SmallVec;

mod instr;

pub use instr::{BlockBuilder, FunctionBuilder, InstrBuilder};

pub struct Signature {
  pub args: Vec<VariableSize>,
  pub rets: Vec<VariableSize>,
}

pub struct Function {
  pub sig:    Signature,
  pub blocks: Vec<Block>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FunctionId(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockId(u32);
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Variable(u32);

impl fmt::Debug for Variable {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "v{}:{:?}", self.id(), self.size())
  }
}

// This gets encoded into the high bits of `Variable`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum VariableSize {
  Bit1,
  Bit8,
  Bit16,
  Bit32,
  Bit64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
  pub instructions: Vec<Instruction>,
  pub terminator:   TerminatorInstruction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
  pub opcode: Opcode,
  pub output: SmallVec<[InstructionOutput; 2]>,
  pub input:  SmallVec<[InstructionInput; 2]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TerminatorInstruction {
  Jump(BlockId),
  Return,
  Trap,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Opcode {
  Math(Math),
  Branch(BlockId),
  Call(FunctionId),
  Compare(Comparison),
  Lea(Symbol),
  Move,
  Syscall,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Math {
  Add,
  Sub,
  Imul,
  Umul,
  Idiv,
  Udiv,
  Irem,
  Urem,
  And,
  Or,
  Xor,
  Shl,
  Ushr,
  Ishr,
  Not,
  Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Comparison {
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
  Imm(u64),
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
  pub const fn new(id: u32, size: VariableSize) -> Self {
    // SAFETY: We need this check to ensure that `size()` is safe.
    assert!(id < (1 << 28), "variable id too large");

    Variable(id | ((size as u32) << 28))
  }

  /// Returns the variable id.
  pub const fn id(&self) -> u32 { self.0 & 0x0fff_ffff }

  pub const fn size(&self) -> VariableSize {
    let bits = (self.0 >> 28) as u8;
    debug_assert!(bits <= VariableSize::Bit64 as u8, "invalid VariableSize bits");
    // SAFETY: `new` ensures that the bits are valid.
    unsafe { std::mem::transmute(bits) }
  }
}

impl From<Variable> for InstructionInput {
  fn from(v: Variable) -> Self { InstructionInput::Var(v) }
}
impl From<u64> for InstructionInput {
  fn from(v: u64) -> Self { InstructionInput::Imm(v) }
}
impl From<Variable> for InstructionOutput {
  fn from(v: Variable) -> Self { InstructionOutput::Var(v) }
}

impl InstructionInput {
  #[track_caller]
  pub fn unwrap_var(self) -> Variable {
    if let InstructionInput::Var(v) = self {
      v
    } else {
      panic!("expected variable input, got {:?}", self);
    }
  }
}

impl InstructionOutput {
  #[track_caller]
  pub fn unwrap_var(self) -> Variable {
    if let InstructionOutput::Var(v) = self {
      v
    } else {
      panic!("expected variable output, got {:?}", self);
    }
  }
}
