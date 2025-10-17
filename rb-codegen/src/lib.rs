use std::fmt;

use smallvec::SmallVec;

mod instr;
mod tvec;

pub use instr::{BlockBuilder, FunctionBuilder, InstrBuilder};
pub use tvec::{TIndex, TVec};

pub struct Signature {
  pub args: Vec<VariableSize>,
  pub rets: Vec<VariableSize>,
}

pub struct Function {
  pub sig:    Signature,
  pub blocks: Vec<Block>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionId(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Variable(u32);

impl<T> TIndex<T> for BlockId {
  fn from_index(index: usize) -> Self { BlockId(index as u32) }
  fn to_index(self) -> usize { self.0 as usize }
}

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
  Branch(Condition, BlockId),
  Compare(Condition),
  Call(FunctionId),
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

impl Function {
  pub fn entry(&self) -> BlockId { BlockId::new(0) }

  pub fn retain_blocks(&mut self, f: impl Fn(BlockId) -> bool) {
    let mut i = 0;
    let mut new_id = 0;
    let mut mapping = TVec::new();
    let old_len = self.blocks.len();
    self.blocks.retain(|_| {
      let id = BlockId::new(i);
      let ret = f(id);
      if ret {
        mapping.push(Some(BlockId::new(new_id)));
        new_id += 1;
      } else {
        mapping.push(None);
      }
      i += 1;
      ret
    });

    if self.blocks.len() != old_len {
      for block in &mut self.blocks {
        for instr in &mut block.instructions {
          match &mut instr.opcode {
            Opcode::Branch(_, target) => {
              let new_id = mapping[*target];
              *target = new_id.expect("retained block has branch to removed block");
            }
            _ => {}
          }
        }

        match &mut block.terminator {
          TerminatorInstruction::Jump(target) => {
            let new_id = mapping[*target];
            *target = new_id.expect("retained block has branch to removed block");
          }
          _ => {}
        }
      }
    }
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

impl fmt::Display for Function {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (i, block) in self.blocks.iter().enumerate() {
      writeln!(f, "block {}:", i)?;
      for instr in &block.instructions {
        writeln!(f, "  {}", instr)?;
      }
      writeln!(f, "  {}", block.terminator)?;
    }
    Ok(())
  }
}

impl fmt::Display for Instruction {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for output in &self.output {
      write!(f, "{} ", output)?;
    }
    write!(f, "= {} ", self.opcode)?;
    for input in &self.input {
      write!(f, "{} ", input)?;
    }
    Ok(())
  }
}

impl fmt::Display for TerminatorInstruction {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      TerminatorInstruction::Jump(target) => write!(f, "jump to block {}", target.as_u32()),
      TerminatorInstruction::Return => write!(f, "return"),
      TerminatorInstruction::Trap => write!(f, "trap"),
    }
  }
}

impl fmt::Display for InstructionOutput {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      InstructionOutput::Var(v) => write!(f, "{:?}", v),
      InstructionOutput::Syscall => write!(f, "syscall"),
    }
  }
}

impl fmt::Display for InstructionInput {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      InstructionInput::Var(v) => write!(f, "{:?}", v),
      InstructionInput::Imm(i) => write!(f, "#{}", i),
    }
  }
}

impl fmt::Display for Opcode {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Opcode::Math(m) => write!(f, "{:?}", m),
      Opcode::Branch(c, target) => write!(f, "branch {:?} to block {}", c, target.as_u32()),
      Opcode::Compare(c) => write!(f, "compare {:?}", c),
      Opcode::Call(func) => write!(f, "call function {}", func.0),
      Opcode::Lea(symbol) => write!(f, "lea symbol {}", symbol.index),
      Opcode::Move => write!(f, "mov"),
      Opcode::Syscall => write!(f, "syscall"),
    }
  }
}
