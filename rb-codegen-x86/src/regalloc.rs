use rb_codegen::{Function, TVec, Variable};
use rb_codegen_opt::analysis::{
  Analysis, control_flow_graph::ControlFlowGraph, dominator_tree::DominatorTree,
};

use crate::Register;

#[derive(Default)]
pub struct VariableRegisters {
  registers: TVec<Variable, Register>,
}

impl VariableRegisters {
  pub fn new() -> Self { VariableRegisters { registers: TVec::new() } }

  pub fn pass(&mut self, function: &mut Function) {
    println!("{function}");

    let mut analysis = Analysis::default();
    analysis.load(ControlFlowGraph::ID, function);
    analysis.load(DominatorTree::ID, function);
    let _cfg = analysis.get::<ControlFlowGraph>();
    let _dom = analysis.get::<DominatorTree>();

    todo!();
  }

  #[track_caller]
  pub fn get(&self, var: Variable) -> Register {
    match self.registers.get(var) {
      Some(reg) => *reg,

      _ => panic!("variable {var:?} is not in a register"),
    }
  }
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

    let mut regs = VariableRegisters::new();
    regs.pass(&mut function.function);

    function.check(expect![@r#"
      block 0:
        mov r0 = 0x01
        mov r1 = 0x00
        mov r5 = r1
        mov r4 = r0
        mov r8 = r2
        mov r10 = r1
        mov r9 = r0
        mov r7 = r9
        mov r6 = r8
        mov r3 = r4
        syscall r3, r5
        mov r2 = 0x02
        syscall r3, r6
        syscall r3, r5
        trap
    "#
    ]);

    assert_eq!(regs.get(v!(r 0)), Register::RAX);
    assert_eq!(regs.get(v!(r 1)), Register::RDI);
    assert_eq!(regs.get(v!(r 2)), Register::RDI);

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
