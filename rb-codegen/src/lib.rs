use std::{collections::BTreeMap, fmt};

use smallvec::SmallVec;

mod instr;
mod tvec;

pub use instr::{BlockBuilder, FunctionBuilder, InstrBuilder};
pub use tvec::{TIndex, TVec};

#[derive(Default, PartialEq, Eq)]
pub struct Signature {
  pub args: Vec<VariableSize>,
  pub rets: Vec<VariableSize>,
}

#[derive(Default, PartialEq, Eq)]
pub struct Function {
  pub sig:          Signature,
  pub blocks:       Vec<Block>,
  pub data:         Vec<u8>,
  pub data_symbols: Vec<SymbolDef>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SymbolDef {
  pub name:   String,
  pub offset: u32,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionId(u32);
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Variable(u32);

impl<T> TIndex<T> for BlockId {
  fn from_index(index: usize) -> Self { BlockId(index as u32) }
  fn to_index(self) -> usize { self.0 as usize }
}

impl<T> TIndex<T> for Variable {
  fn from_index(index: usize) -> Self { Variable::new(index as u32, VariableSize::Bit64) }
  fn to_index(self) -> usize { self.id() as usize }
}

impl fmt::Debug for Variable {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "v{}:{:?}", self.id(), self.size())
  }
}

impl PartialOrd for Variable {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(other)) }
}

impl Ord for Variable {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering { self.id().cmp(&other.id()) }
}

// This gets encoded into the high bits of `Variable`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum VariableSize {
  Bit1,
  Bit8,
  Bit16,
  Bit32,
  Bit64,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Block {
  pub phis:         Vec<Phi>,
  pub instructions: Vec<Instruction>,
  pub terminator:   TerminatorInstruction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Phi {
  pub to:   Variable,
  pub from: BTreeMap<BlockId, Option<Variable>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
  pub opcode: Opcode,
  pub output: SmallVec<[InstructionOutput; 2]>,
  pub input:  SmallVec<[InstructionInput; 2]>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum TerminatorInstruction {
  Jump(BlockId),
  Return(SmallVec<[InstructionInput; 2]>),
  #[default]
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
  Imm(Immediate),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Immediate {
  Signed(i64),
  Unsigned(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionOutput {
  Var(Variable),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Symbol {
  pub index: u32,
}

pub enum AnyInstructionRef<'a> {
  Phi(&'a Phi),
  Instr(&'a Instruction),
  Term(&'a TerminatorInstruction),
}

impl FunctionId {
  pub const fn new(id: u32) -> Self { FunctionId(id) }
  pub const fn as_u32(&self) -> u32 { self.0 }
}
impl BlockId {
  pub const BEFORE: BlockId = BlockId(u32::MAX);
  pub const ENTRY: BlockId = BlockId(0);

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

  pub fn instructions(&self) -> impl Iterator<Item = AnyInstructionRef<'_>> {
    self.blocks.iter().flat_map(|b| b.instructions())
  }

  pub fn blocks(&self) -> impl Iterator<Item = BlockId> + use<> {
    (0..self.blocks.len() as u32).map(BlockId::new)
  }

  pub fn block(&self, id: BlockId) -> &Block { &self.blocks[id.as_u32() as usize] }
  pub fn block_mut(&mut self, id: BlockId) -> &mut Block { &mut self.blocks[id.as_u32() as usize] }

  #[track_caller]
  pub fn two_blocks_mut(&mut self, a: BlockId, b: BlockId) -> (&mut Block, &mut Block) {
    assert!(a != b, "cannot get two mutable references to the same block");

    if a.as_u32() < b.as_u32() {
      let (left, right) = self.blocks.split_at_mut(b.as_u32() as usize);
      (&mut left[a.as_u32() as usize], &mut right[0])
    } else {
      let (left, right) = self.blocks.split_at_mut(a.as_u32() as usize);
      (&mut right[0], &mut left[b.as_u32() as usize])
    }
  }

  pub fn retain_blocks(&mut self, f: impl Fn(BlockId, &mut Block) -> bool) {
    let mut i = 0;
    let mut new_id = 0;
    let mut mapping = TVec::new();
    let old_len = self.blocks.len();
    self.blocks.retain_mut(|block| {
      let id = BlockId::new(i);
      let ret = f(id, block);
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

impl Block {
  fn instructions(&self) -> impl Iterator<Item = AnyInstructionRef<'_>> {
    self
      .phis
      .iter()
      .map(AnyInstructionRef::Phi)
      .chain(self.instructions.iter().map(AnyInstructionRef::Instr))
      .chain(std::iter::once(&self.terminator).map(AnyInstructionRef::Term))
  }
}

enum InstructionInputIter<'a> {
  Phi(std::iter::Flatten<std::collections::btree_map::Values<'a, BlockId, Option<Variable>>>),
  Slice(std::slice::Iter<'a, InstructionInput>),
}
enum InstructionOutputIter<'a> {
  Phi(std::iter::Once<InstructionOutput>),
  Slice(std::slice::Iter<'a, InstructionOutput>),
}

impl Iterator for InstructionInputIter<'_> {
  type Item = InstructionInput;

  fn next(&mut self) -> Option<Self::Item> {
    match self {
      InstructionInputIter::Phi(iter) => iter.next().map(|v| InstructionInput::Var(*v)),
      InstructionInputIter::Slice(iter) => iter.next().copied(),
    }
  }
}

impl Iterator for InstructionOutputIter<'_> {
  type Item = InstructionOutput;

  fn next(&mut self) -> Option<Self::Item> {
    match self {
      InstructionOutputIter::Phi(iter) => iter.next(),
      InstructionOutputIter::Slice(iter) => iter.next().copied(),
    }
  }
}

impl AnyInstructionRef<'_> {
  pub fn outputs(&self) -> impl Iterator<Item = InstructionOutput> {
    match self {
      AnyInstructionRef::Phi(phi) => {
        InstructionOutputIter::Phi(std::iter::once(InstructionOutput::Var(phi.to)))
      }
      AnyInstructionRef::Instr(instr) => InstructionOutputIter::Slice(instr.output.iter()),
      AnyInstructionRef::Term(_) => InstructionOutputIter::Slice([].iter()),
    }
  }

  pub fn inputs(&self) -> impl Iterator<Item = InstructionInput> {
    match self {
      AnyInstructionRef::Phi(phi) => InstructionInputIter::Phi(phi.from.values().flatten()),
      AnyInstructionRef::Instr(instr) => InstructionInputIter::Slice(instr.input.iter()),
      AnyInstructionRef::Term(term) => InstructionInputIter::Slice(match term {
        TerminatorInstruction::Jump(_) => [].iter(),
        TerminatorInstruction::Return(rets) => rets.iter(),
        TerminatorInstruction::Trap => [].iter(),
      }),
    }
  }
}

impl From<Variable> for InstructionInput {
  fn from(v: Variable) -> Self { InstructionInput::Var(v) }
}
impl From<u64> for InstructionInput {
  fn from(v: u64) -> Self { InstructionInput::Imm(Immediate::Unsigned(v)) }
}
impl From<Immediate> for InstructionInput {
  fn from(v: Immediate) -> Self { InstructionInput::Imm(v) }
}
impl From<Variable> for InstructionOutput {
  fn from(v: Variable) -> Self { InstructionOutput::Var(v) }
}

impl Immediate {
  pub fn bits(&self) -> u64 {
    match *self {
      Immediate::Signed(v) => v as u64,
      Immediate::Unsigned(v) => v,
    }
  }

  pub fn is_zero(&self) -> bool { self.bits() == 0 }
}

#[macro_export]
macro_rules! immediate {
  ($a:ident, $op:expr) => {
    match $a {
      $crate::Immediate::Signed(a) => $op(a),
      $crate::Immediate::Unsigned(a) => $op(a),
    }
  };

  ($a:ident, $b:ident, $bin:expr) => {
    match ($a, $b) {
      ($crate::Immediate::Signed(a), $crate::Immediate::Signed(b)) => Some($bin(a, b)),
      ($crate::Immediate::Unsigned(a), $crate::Immediate::Unsigned(b)) => Some($bin(a, b)),
      _ => None,
    }
  };
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
    let InstructionOutput::Var(v) = self;
    v
  }
}

impl fmt::Debug for Function {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Function {{\n{self}}}") }
}

impl fmt::Display for Function {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (i, block) in self.blocks.iter().enumerate() {
      writeln!(f, "block {}:", i)?;
      for phi in &block.phis {
        writeln!(f, "  {}", phi)?;
      }
      for instr in &block.instructions {
        writeln!(f, "  {}", instr)?;
      }
      writeln!(f, "  {}", block.terminator)?;
    }
    Ok(())
  }
}

impl fmt::Display for Phi {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{} = phi(", self.to)?;
    for (i, from) in self.from.iter().enumerate() {
      if i != 0 {
        write!(f, ", ")?;
      }
      if let Some(var) = from.1 {
        write!(f, "{} -> {var}", from.0)?;
      } else {
        write!(f, "{} -> <undef>", from.0)?;
      }
    }
    write!(f, ")")
  }
}

impl fmt::Display for Instruction {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.opcode)?;
    for (i, output) in self.output.iter().enumerate() {
      if i != 0 {
        write!(f, ",")?;
      }
      write!(f, " {}", output)?;
    }
    write!(f, " =")?;
    for (i, input) in self.input.iter().enumerate() {
      if i != 0 {
        write!(f, ",")?;
      }
      write!(f, " {}", input)?;
    }
    Ok(())
  }
}

impl fmt::Display for TerminatorInstruction {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      TerminatorInstruction::Jump(target) => write!(f, "jump to block {}", target.as_u32()),
      TerminatorInstruction::Return(rets) => {
        write!(f, "return")?;
        for (i, ret) in rets.iter().enumerate() {
          if i != 0 {
            write!(f, ",")?;
          }
          write!(f, " {}", ret)?;
        }
        Ok(())
      }
      TerminatorInstruction::Trap => write!(f, "trap"),
    }
  }
}

impl fmt::Display for InstructionOutput {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      InstructionOutput::Var(v) => write!(f, "{v}"),
    }
  }
}

impl fmt::Display for InstructionInput {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      InstructionInput::Var(v) => write!(f, "{v}"),
      InstructionInput::Imm(i) => write!(f, "{:#04x}", i.bits()),
    }
  }
}

impl fmt::Display for Opcode {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Opcode::Math(m) => write!(f, "math({m})"),
      Opcode::Branch(c, target) => write!(f, "branch {c:?} to {target}"),
      Opcode::Compare(c) => write!(f, "compare {c:?}"),
      Opcode::Call(func) => write!(f, "call function {}", func.0),
      Opcode::Lea(symbol) => write!(f, "lea symbol {}", symbol.index),
      Opcode::Move => write!(f, "mov"),
      Opcode::Syscall => write!(f, "syscall"),
    }
  }
}

impl fmt::Display for Math {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Math::Add => write!(f, "add"),
      Math::Sub => write!(f, "sub"),
      Math::Imul => write!(f, "imul"),
      Math::Umul => write!(f, "umul"),
      Math::Idiv => write!(f, "idiv"),
      Math::Udiv => write!(f, "udiv"),
      Math::Irem => write!(f, "irem"),
      Math::Urem => write!(f, "urem"),
      Math::And => write!(f, "and"),
      Math::Or => write!(f, "or"),
      Math::Xor => write!(f, "xor"),
      Math::Shl => write!(f, "shl"),
      Math::Ushr => write!(f, "ushr"),
      Math::Ishr => write!(f, "ishr"),
      Math::Not => write!(f, "not"),
      Math::Neg => write!(f, "neg"),
    }
  }
}

impl fmt::Display for Variable {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "{}{}",
      match self.size() {
        VariableSize::Bit1 => "b",
        VariableSize::Bit8 => "l",
        VariableSize::Bit16 => "x",
        VariableSize::Bit32 => "e",
        VariableSize::Bit64 => "r",
      },
      self.id(),
    )
  }
}

impl fmt::Display for BlockId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if *self == BlockId::BEFORE {
      write!(f, "block before")
    } else {
      write!(f, "block {}", self.as_u32())
    }
  }
}
