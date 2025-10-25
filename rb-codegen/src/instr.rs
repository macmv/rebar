use std::collections::BTreeMap;

use smallvec::smallvec;

use crate::{
  Block, BlockId, Condition, Function, FunctionId, InstructionInput, Math, Signature, Symbol,
  SymbolDef, Variable, VariableSize,
};

pub struct FunctionBuilder {
  next_variable: u32,
  function:      Function,
  terminated:    Vec<bool>,
  block:         BlockId,
}

pub struct BlockBuilder<'a> {
  function: &'a mut FunctionBuilder,
  block:    BlockId,
}

pub struct InstrBuilder<'a> {
  function: &'a mut FunctionBuilder,
  block:    BlockId,
}

impl FunctionBuilder {
  pub fn new(sig: Signature) -> Self {
    FunctionBuilder {
      next_variable: sig.args.len() as u32,
      function:      Function {
        sig,
        blocks: vec![Block::default()],
        data: vec![],
        data_symbols: vec![],
      },
      terminated:    vec![false],
      block:         BlockId(0),
    }
  }

  pub fn add_data(&mut self, data: &[u8]) -> Symbol {
    let offset = self.function.data.len() as u32;
    self.function.data.extend_from_slice(data);

    let symbol = Symbol { index: self.function.data_symbols.len() as u32 };
    self.function.data_symbols.push(SymbolDef { name: format!("str{offset}"), offset });
    symbol
  }

  pub fn build(self) -> Function { self.function }

  pub fn arg(&self, index: u32) -> crate::Variable {
    assert!(
      index < self.function.sig.args.len() as u32,
      "arg index {index} >= args {}",
      self.function.sig.args.len(),
    );

    Variable::new(index, self.function.sig.args[index as usize])
  }

  pub fn var(&mut self, size: VariableSize) -> crate::Variable {
    let var = Variable::new(self.next_variable, size);
    self.next_variable += 1;
    var
  }

  pub fn new_block(&mut self) -> BlockBuilder<'_> {
    let id = BlockId(self.function.blocks.len() as u32);
    self.function.blocks.push(Block::default());
    self.terminated.push(false);

    self.block(id)
  }

  pub fn block(&mut self, id: BlockId) -> BlockBuilder<'_> {
    BlockBuilder { function: self, block: id }
  }

  pub fn switch_to(&mut self, id: BlockId) { self.block = id; }
  pub fn current_block(&mut self) -> BlockBuilder<'_> { self.block(self.block) }

  pub fn instr(&mut self) -> InstrBuilder<'_> {
    InstrBuilder { block: self.current_block().id(), function: self }
  }
}

impl BlockBuilder<'_> {
  pub fn id(&self) -> BlockId { self.block }

  pub fn is_terminated(&self) -> bool { self.function.terminated[self.block.0 as usize] }

  #[track_caller]
  pub fn phi(&mut self, from: BTreeMap<BlockId, Option<Variable>>) -> Variable {
    assert!(
      self.function.function.blocks[self.block.0 as usize].instructions.is_empty(),
      "phis must proceed other instructions",
    );
    assert!(!self.is_terminated(), "cannot add phi to terminated block");

    let size = from.values().flatten().next().expect("phi cannot be empty").size();
    assert!(
      from.values().flatten().all(|v| v.size() == size),
      "phi inputs must have the same size"
    );

    let to = self.function.var(size);
    self.function.function.blocks[self.block.0 as usize].phis.push(crate::Phi { from, to });
    to
  }

  #[track_caller]
  pub fn instr(&mut self) -> InstrBuilder<'_> {
    assert!(!self.is_terminated(), "cannot add instruction to terminated block");

    InstrBuilder { function: self.function, block: self.block }
  }

  #[track_caller]
  pub fn terminate(self, term: crate::TerminatorInstruction) {
    if !self.is_terminated() {
      self.function.function.blocks[self.block.0 as usize].terminator = term;
      self.function.terminated[self.block.0 as usize] = true;
    }
  }
}

macro_rules! instructions {
  ($(
    $name:ident:
    $variant:ident $(($($param:ident: $param_ty:ty),*))? =>
    $($input:ident),*
  );* $(;)?) => {
    impl InstrBuilder<'_> {
      $(
        pub fn $name(
          self,
          $($($param: $param_ty,)*)*
          output: VariableSize,
          $($input: impl Into<InstructionInput>,)*
        ) -> Variable {
          let output = self.function.var(output);

          self.function.function.blocks[self.block.0 as usize].instructions.push(crate::Instruction {
            opcode: crate::Opcode::$variant $(($( $param ),*))?,
            input:  smallvec![$($input.into(),)*],
            output: smallvec![output.into()],
          });

          output
        }
      )*
    }
  };
}

instructions! {
  math1: Math(math: Math) => input;
  math2: Math(math: Math) => input1, input2;
  branch: Branch(condition: Condition, block: BlockId) => input1, input2;
  cmp: Compare(condition: Condition) => input1, input2;
  lea: Lea(symbol: Symbol) => ;
  mov: Move => input;
  syscall1: Syscall => input;
  syscall2: Syscall => input1, input2;
  syscall3: Syscall => input1, input2, input3;
  syscall4: Syscall => input1, input2, input3, input4;
}

impl InstrBuilder<'_> {
  pub fn call(self, function: FunctionId, args: &[InstructionInput]) -> Variable {
    let output = self.function.var(VariableSize::Bit64);

    self.function.function.blocks[self.block.0 as usize].instructions.push(crate::Instruction {
      opcode: crate::Opcode::Call(function),
      input:  args.into_iter().copied().collect(),
      output: smallvec![output.into()],
    });

    output
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn codegen_asm() {
    let mut builder = FunctionBuilder::new(Signature {
      args: vec![VariableSize::Bit64, VariableSize::Bit64],
      rets: vec![],
    });

    let arg1 = builder.arg(0);
    let arg2 = builder.arg(1);

    let mut block = builder.new_block();
    let _res = block.instr().math2(Math::Add, VariableSize::Bit64, arg1, arg2);
    let _addr = block.instr().lea(Symbol { index: 2 }, VariableSize::Bit64);
  }
}
