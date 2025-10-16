use smallvec::smallvec;

use crate::{
  Block, BlockId, Condition, Function, InstructionInput, Signature, Symbol, Variable, VariableSize,
};

pub struct FunctionBuilder {
  next_variable: u32,
  function:      Function,
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
    }
  }

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

    self.block(id)
  }

  pub fn block(&mut self, id: BlockId) -> BlockBuilder<'_> {
    BlockBuilder { function: self, block: id }
  }

  pub fn last_block(&mut self) -> BlockBuilder<'_> {
    let id = BlockId((self.function.blocks.len() - 1) as u32);
    self.block(id)
  }

  pub fn instr(&mut self) -> InstrBuilder<'_> {
    InstrBuilder { block: self.last_block().id(), function: self }
  }
}

impl BlockBuilder<'_> {
  pub fn id(&self) -> BlockId { self.block }

  pub fn instr(&mut self) -> InstrBuilder<'_> {
    InstrBuilder { function: self.function, block: self.block }
  }
}

macro_rules! instructions {
  ($(
    $name:ident:
    $variant:ident $(($($param:ident: $param_ty:ty),*))? =>
    $($output:ident),*
    $(: $($input:ident),+)?
  );* $(;)?) => {
    impl InstrBuilder<'_> {
      $(
        pub fn $name(
          self,
          $($($param: $param_ty,)*)*
          $($output: VariableSize,)*
          $($($input: impl Into<InstructionInput>,)+)?
        ) -> ($(ignore!($output => Variable),)*) {
          $(
            let $output = self.function.var($output);
          )*

          self.function.function.blocks[self.block.0 as usize].instructions.push(crate::Instruction {
            opcode: crate::Opcode::$variant $(($( $param ),*))?,
            input:  smallvec![$($($input.into(),)+)?],
            output: smallvec![$($output.into(),)*],
          });

          (
            $($output,)*
          )
        }
      )*
    }
  };
}

macro_rules! ignore {
  ($var:ident => $tt:tt) => {
    $tt
  };
}

instructions! {
  add: Add => output : input1, input2;
  lea: Lea(symbol: Symbol) => output;
  mov: Move => output : input;
  branch: Branch(condition: Condition, block: BlockId) => input;
  syscall1: Syscall => output : input;
  syscall2: Syscall => output : input1, input2;
  syscall3: Syscall => output : input1, input2, input3;
  syscall4: Syscall => output : input1, input2, input3, input4;
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
    let _res = block.instr().add(VariableSize::Bit64, arg1, arg2);
    let _addr = block.instr().lea(Symbol { index: 2 }, VariableSize::Bit64);
  }
}
