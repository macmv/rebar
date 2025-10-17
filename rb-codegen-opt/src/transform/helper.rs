use rb_codegen::{Block, Function, Instruction, InstructionInput, InstructionOutput, Variable};

pub trait InstructionViewMut {
  // type PhiIter<'a>: Iterator<Item = &'a mut Phi>
  // where
  //   Self: 'a;
  type InstrIter<'a>: Iterator<Item = &'a mut Instruction>
  where
    Self: 'a;

  // fn phis(&mut self) -> Self::PhiIter<'_>;
  fn instructions(&mut self) -> Self::InstrIter<'_>;
}

impl InstructionViewMut for &mut [Instruction] {
  // type PhiIter<'a>
  //   = std::iter::Empty<&'a mut Phi>
  // where
  //   Self: 'a;
  type InstrIter<'a>
    = std::slice::IterMut<'a, Instruction>
  where
    Self: 'a;

  // fn phis(&mut self) -> Self::PhiIter<'_> { std::iter::empty() }
  fn instructions(&mut self) -> Self::InstrIter<'_> { self.iter_mut() }
}

impl InstructionViewMut for &mut [Block] {
  // type PhiIter<'a>
  //   = std::iter::FlatMap<
  //   std::slice::IterMut<'a, Block>,
  //   std::slice::IterMut<'a, Phi>,
  //   fn(&'a mut Block) -> std::slice::IterMut<'a, Phi>,
  // >
  // where
  //   Self: 'a;
  type InstrIter<'a>
    = std::iter::FlatMap<
    std::slice::IterMut<'a, Block>,
    std::slice::IterMut<'a, Instruction>,
    fn(&'a mut Block) -> std::slice::IterMut<'a, Instruction>,
  >
  where
    Self: 'a;

  // fn phis(&mut self) -> Self::PhiIter<'_> { self.iter_mut().flat_map(|b|
  // b.phis.iter_mut()) }
  fn instructions(&mut self) -> Self::InstrIter<'_> {
    self.iter_mut().flat_map(|b| b.instructions.iter_mut())
  }
}

impl InstructionViewMut for &mut Function {
  // type PhiIter<'a>
  //   = std::iter::FlatMap<
  //   std::slice::IterMut<'a, Block>,
  //   std::slice::IterMut<'a, Phi>,
  //   fn(&'a mut Block) -> std::slice::IterMut<'a, Phi>,
  // >
  // where
  //   Self: 'a;
  type InstrIter<'a>
    = std::iter::FlatMap<
    std::slice::IterMut<'a, Block>,
    std::slice::IterMut<'a, Instruction>,
    fn(&'a mut Block) -> std::slice::IterMut<'a, Instruction>,
  >
  where
    Self: 'a;

  // fn phis(&mut self) -> Self::PhiIter<'_> { self.blocks.iter_mut().flat_map(|b|
  // b.phis.iter_mut()) }
  fn instructions(&mut self) -> Self::InstrIter<'_> {
    self.blocks.iter_mut().flat_map(|b| b.instructions.iter_mut())
  }
}

pub fn replace_variable(view: impl InstructionViewMut, from: Variable, to: Variable) {
  transform_variables(view, |v| {
    if *v == from {
      *v = to;
    }
  });
}

pub fn transform_variables(mut view: impl InstructionViewMut, transform: impl Fn(&mut Variable)) {
  /*
  for phi in view.phis() {
    for from in phi.from.values_mut() {
      transform(from);
    }
    transform(&mut phi.to.id);
  }
  */

  for instr in view.instructions() {
    for input in &mut instr.input {
      if let InstructionInput::Var(var) = input {
        transform(var);
      }
    }
    for output in &mut instr.output {
      if let InstructionOutput::Var(var) = output {
        transform(var);
      }
    }
  }
}
