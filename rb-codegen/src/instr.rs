use smallvec::smallvec;

use crate::{
  Block, BlockId, Condition, Function, Instruction, InstructionInput, InstructionOutput, Signature,
  Symbol, Variable, VariableSize,
};

pub struct FunctionBuilder {
  next_variable: u32,
  function:      Function,
}

pub struct BlockBuilder<'a> {
  block: &'a mut Block,
  id:    BlockId,
}

pub struct InstrBuilder<'a> {
  instruction: &'a mut Instruction,
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
    BlockBuilder { block: &mut self.function.blocks[id.0 as usize], id }
  }
}

impl BlockBuilder<'_> {
  pub fn id(&self) -> BlockId { self.id }

  pub fn instr(&mut self) -> InstrBuilder<'_> {
    self.block.instructions.push(crate::Instruction {
      opcode: crate::Opcode::Add,
      input:  smallvec![],
      output: smallvec![],
    });
    InstrBuilder { instruction: self.block.instructions.last_mut().unwrap() }
  }
}

macro_rules! instructions {
  ($(
    $name:ident:
    $variant:ident $(($($param:ident: $param_ty:ty),*))? =>
    $($input:ident),*
    $(: $($output:ident),+)?
  );* $(;)?) => {
    $(
      impl InstrBuilder<'_> {
        pub fn $name(
          self,
          $($($param: $param_ty,)*)*
          $($($output: impl Into<InstructionOutput>,)+)?
          $($input: impl Into<InstructionInput>,)*
        ) {
          self.instruction.opcode = crate::Opcode::$variant $(($( $param ),*))?;
          self.instruction.input = smallvec![$($input.into(),)*];
          self.instruction.output = smallvec![$($($output.into(),)+)?];
        }
      }
    )*
  };
}

instructions! {
  add: Add => output : input1, input2;
  lea: Lea(symbol: Symbol) => output;
  mov: Move => output : input;
  branch: Branch(condition: Condition, block: BlockId) => input;
  syscall1: Syscall => input : output;
  syscall2: Syscall => input1, input2 : output;
  syscall3: Syscall => input1, input2, input3 : output;
  syscall4: Syscall => input1, input2, input3, input4 : output;
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

    let res = builder.var(VariableSize::Bit64);

    let mut block = builder.new_block();
    block.instr().add(res, arg1, arg2);
    block.instr().lea(Symbol { index: 2 }, res);
  }
}
