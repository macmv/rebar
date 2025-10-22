use std::collections::{HashMap, HashSet};

use rb_codegen::{
  Block, BlockId, Function, Instruction, InstructionInput, InstructionOutput, TVec, Variable,
};
use rb_codegen_opt::analysis::{
  Analysis, control_flow_graph::ControlFlowGraph, dominator_tree::DominatorTree,
};

use crate::{Register, RegisterIndex, var_to_reg_size};

#[derive(Default)]
pub struct VariableRegisters {
  registers: TVec<Variable, Register>,
}

struct Regalloc<'a> {
  cfg:   &'a ControlFlowGraph,
  dom:   &'a DominatorTree,
  alloc: &'a mut VariableRegisters,

  active:        HashMap<RegisterIndex, Variable>,
  future_active: HashMap<Variable, RegisterIndex>,
  visited:       HashSet<BlockId>,
}

impl VariableRegisters {
  pub fn pass(function: &mut Function) -> Self {
    println!("{function}");

    let mut analysis = Analysis::default();
    analysis.load(ControlFlowGraph::ID, function);
    analysis.load(DominatorTree::ID, function);
    let _dom = analysis.get::<DominatorTree>();

    let mut regs = VariableRegisters::default();
    let mut regalloc = Regalloc {
      cfg:   analysis.get(),
      dom:   analysis.get(),
      alloc: &mut regs,

      active:        HashMap::new(),
      future_active: HashMap::new(),
      visited:       HashSet::new(),
    };
    regalloc.pass(function);

    regs
  }

  #[track_caller]
  pub fn get(&self, var: Variable) -> Register {
    match self.registers.get(var) {
      Some(reg) => *reg,

      _ => panic!("variable {var:?} is not in a register"),
    }
  }
}

impl Regalloc<'_> {
  pub fn pass(&mut self, function: &Function) {
    self.pre_allocation();

    let mut live_outs = HashSet::new();

    for block in self.dom.preorder() {
      let live_ins = HashSet::new(); // "set of instructions live into `block`"

      self.expire_intervals(&live_ins, &live_outs);
      self.start_intervals(&live_ins, &live_outs);

      for (i, instr) in function.block(block).instructions.iter().enumerate() {
        self.expire_instr_intervals(
          &mut live_outs,
          &function.block(block).instructions[i..],
          instr,
        );

        let &[InstructionOutput::Var(out)] = instr.output.as_slice() else { continue };
        self.allocate(out);
        live_outs.insert(out);
      }

      self.visited.insert(block);
    }
  }

  fn pre_allocation(&mut self) {
    // TODO: Pin variables to registers based on constraints.
    self
      .future_active
      .insert(Variable::new(0, rb_codegen::VariableSize::Bit64), RegisterIndex::Eax);
    self
      .future_active
      .insert(Variable::new(1, rb_codegen::VariableSize::Bit64), RegisterIndex::Edx);
    self
      .future_active
      .insert(Variable::new(2, rb_codegen::VariableSize::Bit64), RegisterIndex::Edx);
  }

  fn expire_intervals(&mut self, live_ins: &HashSet<Variable>, live_outs: &HashSet<Variable>) {
    for &var in live_outs.iter().filter(|&&v| !live_ins.contains(&v)) {
      self.free(var);
    }
  }

  fn start_intervals(&mut self, live_ins: &HashSet<Variable>, live_outs: &HashSet<Variable>) {
    for &var in live_ins.iter().filter(|&&v| !live_outs.contains(&v)) {
      self.allocate(var);
    }
  }

  fn expire_instr_intervals(
    &mut self,
    live_outs: &mut HashSet<Variable>,
    block_after_instr: &[Instruction],
    instr: &Instruction,
  ) {
    for input in &instr.input {
      let &InstructionInput::Var(var) = input else { continue };

      live_outs.remove(&var);
      if is_used_later_in_block(block_after_instr, var) {
        self.pause(var);
      } else {
        self.free(var);
      }
    }
  }

  fn allocate(&mut self, var: Variable) {
    println!("allocating {var}");
    let reg = self.future_active.remove(&var).unwrap_or_else(|| self.pick_register(var));
    self.active.insert(reg, var);
    self
      .alloc
      .registers
      .set(var, Register { size: var_to_reg_size(var.size()).unwrap(), index: reg });
  }

  fn pause(&mut self, var: Variable) {
    println!("pausing {var}");
    match self.active.iter().find(|&(_, &v)| v == var) {
      Some((&reg, _)) => {
        self.active.remove(&reg);
        self.future_active.insert(var, reg);
      }
      None => {}
    }
  }

  fn free(&mut self, var: Variable) {
    println!("freeing {var}");
    match self.active.iter().find(|&(_, &v)| v == var) {
      Some((&reg, _)) => {
        self.active.remove(&reg);
      }
      None => {}
    }
  }

  fn pick_register(&self, var: Variable) -> RegisterIndex {
    for reg_index in 0..16 {
      let reg_index = RegisterIndex::from_usize(reg_index);

      if !self.active.contains_key(&reg_index) {
        return reg_index;
      }
    }

    panic!("no registers available for variable {var:?}");
  }
}

fn is_used_later_in_block(block: &[Instruction], var: Variable) -> bool {
  for instr in block.iter().skip(1) {
    for input in &instr.input {
      if let InstructionInput::Var(v) = input {
        if *v == var {
          return true;
        }
      }
    }
  }

  false
}

#[cfg(test)]
mod tests {
  use rb_codegen::{Variable, VariableSize};
  use rb_codegen_opt::parse;
  use rb_test::expect;

  use crate::regalloc::{Register, VariableRegisters};

  macro_rules! v {
    ($size:tt $index:expr) => {
      Variable::new($index, size!($size))
    };
  }

  macro_rules! size {
    (r) => {
      VariableSize::Bit64
    };
  }

  #[test]
  fn simple_syscall() {
    let mut function = parse(
      "
      block 0:
        mov r0 = 0x01
        mov r1 = 0x00
        syscall r0, r1
        mov r2 = 0x02
        syscall r0, r2
        syscall r0, r1
      ",
    );

    let regs = VariableRegisters::pass(&mut function.function);

    function.check(expect![@r#"
      block 0:
        mov r0 = 0x01
        mov r1 = 0x00
        syscall r0, r1
        mov r2 = 0x02
        syscall r0, r2
        syscall r0, r1
        trap
    "#
    ]);

    assert_eq!(regs.get(v!(r 0)), Register::RAX);
    assert_eq!(regs.get(v!(r 1)), Register::RDX);
    assert_eq!(regs.get(v!(r 2)), Register::RDX);

    panic!();
  }

  #[ignore]
  #[test]
  fn big_syscall() {
    parse(
      "
      block 0:
        mov r0 = 0xffffff
        mov r1 = 0x03
        mov r2 = 0x01
        mov r3 = 0x00
        syscall r2, r3, r0, r1
        mov r5 = 0xffffff
        mov r6 = 0x0e
        mov r7 = 0x01
        mov r8 = 0x00
        syscall r7, r8, r5, r6
        mov r10 = 0x04
        mov r11 = 0x03
        branch Greater to block 1 r12 = r10, r11
        jump to block 2
      block 1:
        jump to block 2
      block 2:
        r13 = phi(block 0 -> r0, block 1 -> r5)
        r14 = phi(block 0 -> r1, block 1 -> r6)
        mov r15 = 0x01
        mov r16 = 0x00
        syscall r15, r16, r13, r14
        mov r18 = 0x3c
        mov r19 = 0x00
        syscall r18, r19
        mov r21 = 0x00
        return r21",
    );
  }
}
