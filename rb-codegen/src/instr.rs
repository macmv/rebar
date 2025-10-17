use smallvec::smallvec;

use crate::{
  Block, BlockId, Comparison, Function, FunctionId, InstructionInput, Math, Signature, Symbol,
  Variable, VariableSize,
};

pub struct FunctionBuilder {
  next_variable: u32,
  function:      Function,
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
      next_variable: 0,
      function:      Function {
        sig,
        blocks: vec![Block {
          instructions: vec![],
          terminator:   crate::TerminatorInstruction::Trap,
        }],
      },
      block:         BlockId(0),
    }
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
    self
      .function
      .blocks
      .push(Block { instructions: vec![], terminator: crate::TerminatorInstruction::Trap });

    self.block = id;
    self.current_block()
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

  pub fn terminate(self, term: crate::TerminatorInstruction) {
    self.function.function.blocks[self.block.0 as usize].terminator = term;
  }

  pub fn instr(&mut self) -> InstrBuilder<'_> {
    InstrBuilder { function: self.function, block: self.block }
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
  branch: Branch(block: BlockId) => input;
  call: Call(function: FunctionId) => input;
  cmp: Compare(cmp: Comparison) => input1, input2;
  lea: Lea(symbol: Symbol) => ;
  mov: Move => input;
  syscall1: Syscall => input;
  syscall2: Syscall => input1, input2;
  syscall3: Syscall => input1, input2, input3;
  syscall4: Syscall => input1, input2, input3, input4;
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
