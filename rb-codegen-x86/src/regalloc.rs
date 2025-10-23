use std::collections::{BTreeMap, HashMap, HashSet};

use rb_codegen::{
  BlockId, Function, Immediate, Instruction, InstructionInput, InstructionOutput, Opcode, TVec,
  Variable, VariableSize,
};
use rb_codegen_opt::analysis::{
  Analysis, control_flow_graph::ControlFlowGraph, dominator_tree::DominatorTree,
};
use smallvec::smallvec;

use crate::{Register, RegisterIndex, var_to_reg_size};

#[derive(Default)]
pub struct VariableRegisters {
  registers: TVec<Variable, Register>,
}

struct Regalloc<'a> {
  dom:   &'a DominatorTree,
  alloc: &'a mut VariableRegisters,

  active:  HashMap<RegisterIndex, Variable>,
  visited: HashSet<BlockId>,

  preference: HashMap<Variable, RegisterIndex>,

  next_variable: u32,
  copies:        BTreeMap<InstructionLocation, Vec<Move>>,
}

#[derive(Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct InstructionLocation {
  block: BlockId,
  index: usize,
}

enum Move {
  VarReg { from: Variable, to: RegisterIndex },
  VarVar { from: Variable, to: Variable },
  ImmVar { from: Immediate, to: Variable },
}

impl VariableRegisters {
  pub fn pass(function: &mut Function) -> Self {
    println!("{function}");

    let mut analysis = Analysis::default();
    analysis.load(ControlFlowGraph::ID, function);
    analysis.load(DominatorTree::ID, function);
    let _dom = analysis.get::<DominatorTree>();

    let last_variable = function
      .blocks()
      .flat_map(|b| function.block(b).instructions.iter())
      .flat_map(|instr| {
        instr
          .input
          .iter()
          .filter_map(|input| match input {
            InstructionInput::Var(v) => Some(v.id()),
            _ => None,
          })
          .chain(instr.output.iter().filter_map(|output| match output {
            InstructionOutput::Var(v) => Some(v.id()),
          }))
      })
      .max();

    let mut regs = VariableRegisters::default();
    let mut regalloc = Regalloc {
      dom:   analysis.get(),
      alloc: &mut regs,

      active:        HashMap::new(),
      visited:       HashSet::new(),
      preference:    HashMap::new(),
      next_variable: last_variable.map(|v| v + 1).unwrap_or(0),
      copies:        BTreeMap::new(),
    };
    regalloc.pass(function);

    for (loc, moves) in regalloc.copies.iter().rev() {
      let block = function.block_mut(loc.block);
      for m in moves.iter().rev() {
        match m {
          Move::VarReg { from, to } => {
            let new_var = Variable::new(regalloc.next_variable, from.size());
            regalloc.next_variable += 1;

            block.instructions.insert(
              loc.index,
              Instruction {
                opcode: Opcode::Move,
                input:  smallvec![(*from).into()],
                output: smallvec![new_var.into()],
              },
            );
            regalloc.alloc.registers.set(
              new_var,
              Register { size: var_to_reg_size(new_var.size()).unwrap(), index: *to },
            );
          }
          Move::VarVar { from, to } => {
            block.instructions.insert(
              loc.index,
              Instruction {
                opcode: Opcode::Move,
                input:  smallvec![(*from).into()],
                output: smallvec![(*to).into()],
              },
            );
          }
          Move::ImmVar { from, to } => {
            block.instructions.insert(
              loc.index,
              Instruction {
                opcode: Opcode::Move,
                input:  smallvec![(*from).into()],
                output: smallvec![(*to).into()],
              },
            );
          }
        }
      }
    }

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
  pub fn pass(&mut self, function: &mut Function) {
    self.pre_allocation(function);

    let mut live_outs = HashSet::new();

    for block in self.dom.preorder() {
      let live_ins = HashSet::new(); // "set of instructions live into `block`"

      self.expire_intervals(&live_ins, &live_outs);
      self.start_intervals(&live_ins, &live_outs);

      for i in 0..function.block(block).instructions.len() {
        self.visit_instr(
          InstructionLocation { block, index: i },
          &mut function.block_mut(block).instructions[i],
        );

        let instr = &function.block(block).instructions[i];

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

  fn pre_allocation(&mut self, function: &Function) {
    for block in function.blocks() {
      for instr in &function.block(block).instructions {
        if instr.opcode != Opcode::Syscall {
          continue;
        }

        for (i, &input) in instr.input.iter().enumerate() {
          let InstructionInput::Var(var) = input else { continue };

          let reg_index = match i {
            0 => RegisterIndex::Eax,
            1 => RegisterIndex::Edx,
            2 => RegisterIndex::Ecx,
            3 => RegisterIndex::Ebx,
            4 => RegisterIndex::Esi,
            5 => RegisterIndex::Edi,
            _ => unreachable!(),
          };

          self.preference.insert(var, reg_index);
        }
      }
    }
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
      if !is_used_later_in_block(block_after_instr, var) {
        self.free(var);
      }
    }
  }

  /// Visiting an instructtion does two things:
  /// - Satisfies register requirements. Some registers may be prefered, but
  ///   variables won't always be allocated to their preference. So, this is
  ///   where we add moves to fix that.
  /// - Move registers we still need that get clobbered.
  fn visit_instr(&mut self, loc: InstructionLocation, instr: &mut Instruction) {
    let mut moves = vec![];

    for (i, input) in instr.input.iter_mut().enumerate() {
      let requirement = match instr.opcode {
        Opcode::Syscall => match i {
          0 => Some(RegisterIndex::Eax),
          1 => Some(RegisterIndex::Edx),
          2 => Some(RegisterIndex::Ecx),
          3 => Some(RegisterIndex::Ebx),
          4 => Some(RegisterIndex::Esi),
          5 => Some(RegisterIndex::Edi),
          _ => unreachable!(),
        },
        _ => None,
      };

      let Some(requirement) = requirement else { continue };

      match input {
        InstructionInput::Var(v) => match self.active.get(&requirement) {
          Some(active) if active == v => {}
          Some(other) => {
            println!("saving {other}");
            moves.push(Move::VarReg { from: *other, to: RegisterIndex::Edi });

            println!("moving {v} -> {requirement:?}");
            let new_var = self.fresh_var(v.size());
            moves.push(Move::VarVar { from: *v, to: new_var });
            self.alloc.registers.set_with(
              new_var,
              Register { size: var_to_reg_size(v.size()).unwrap(), index: requirement },
              || Register::RAX,
            );
            *v = new_var;
          }
          None => {
            println!("moving {v} -> {requirement:?}");
            moves.push(Move::VarReg { from: *v, to: requirement });
          }
        },
        InstructionInput::Imm(imm) => match self.active.get(&requirement) {
          Some(other) => {
            println!("saving {other}");
            moves.push(Move::VarReg { from: *other, to: RegisterIndex::Edi });

            println!("moving new -> {requirement:?}");
            let new_var = self.fresh_var(imm.size());
            moves.push(Move::ImmVar { from: *imm, to: new_var });
            self.alloc.registers.set_with(
              new_var,
              Register { size: var_to_reg_size(imm.size()).unwrap(), index: requirement },
              || Register::RAX,
            );
            *input = InstructionInput::Var(new_var);
          }
          None => {
            println!("moving new -> {requirement:?}");
            let new_var = self.fresh_var(imm.size());
            moves.push(Move::ImmVar { from: *imm, to: new_var });
            self.alloc.registers.set_with(
              new_var,
              Register { size: var_to_reg_size(imm.size()).unwrap(), index: requirement },
              || Register::RAX,
            );
            *input = InstructionInput::Var(new_var);
          }
        },
      }
    }

    if !moves.is_empty() {
      self.copies.insert(loc, moves);
    }

    // TODO
    /*
    let clobbers: &[RegisterIndex] = match instr.opcode {
      Opcode::Syscall => &[
        RegisterIndex::Eax,
        RegisterIndex::Ecx,
        RegisterIndex::Edx,
        RegisterIndex::Ebx,
        RegisterIndex::Esi,
        RegisterIndex::Edi,
      ],
      _ => &[],
    };

    for clobber in clobbers {
      if let Some(&var) = self.active.get(clobber) {
        println!("clobbering {var} in {clobber:?}");
      }
    }
    */
  }

  fn fresh_var(&mut self, size: VariableSize) -> Variable {
    let v = Variable::new(self.next_variable, size);
    self.next_variable += 1;
    v
  }

  fn allocate(&mut self, var: Variable) {
    let reg = self.pick_register(var);
    println!("allocating {var} = {reg:?}");
    self.active.insert(reg, var);
    self
      .alloc
      .registers
      .set(var, Register { size: var_to_reg_size(var.size()).unwrap(), index: reg });
  }

  fn free(&mut self, var: Variable) {
    match self.active.iter().find(|&(_, &v)| v == var) {
      Some((&reg, _)) => {
        println!("freeing {var} in {reg:?}");
        self.active.remove(&reg);
      }
      None => {
        println!("freeing {var} (none)");
      }
    }
  }

  fn pick_register(&self, var: Variable) -> RegisterIndex {
    if let Some(pref) = self.preference.get(&var) {
      if !self.active.contains_key(pref) {
        return *pref;
      }
    }

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
        mov r3 = 0x03
        syscall r3, r1
      ",
    );

    let regs = VariableRegisters::pass(&mut function.function);

    function.check(expect![@r#"
      block 0:
        mov r0 = 0x01
        mov r1 = 0x00
        syscall r0, r1
        mov r2 = 0x02
        mov r5 = r1
        mov r4 = r2
        syscall r0, r4
        mov r3 = 0x03
        syscall r3, r1
        trap
    "#
    ]);

    assert_eq!(regs.get(v!(r 0)), Register::RAX);
    assert_eq!(regs.get(v!(r 1)), Register::RDX);
    assert_eq!(regs.get(v!(r 2)), Register::RCX);
    assert_eq!(regs.get(v!(r 3)), Register::RAX);
    assert_eq!(regs.get(v!(r 4)), Register::RDX);
    assert_eq!(regs.get(v!(r 5)), Register::RDI);
  }

  #[test]
  fn syscall_with_imm() {
    let mut function = parse(
      "
      block 0:
        syscall 0x00, 0x01
        syscall 0x00, 0x02
        syscall 0x00, 0x03
      ",
    );

    let regs = VariableRegisters::pass(&mut function.function);

    function.check(expect![@r#"
      block 0:
        mov r0 = 0x00
        mov r1 = 0x01
        syscall r0, r1
        mov r2 = 0x00
        mov r3 = 0x02
        syscall r2, r3
        mov r4 = 0x00
        mov r5 = 0x03
        syscall r4, r5
        trap
    "#
    ]);

    assert_eq!(regs.get(v!(r 0)), Register::RAX);
    assert_eq!(regs.get(v!(r 1)), Register::RDX);
    assert_eq!(regs.get(v!(r 2)), Register::RAX);
    assert_eq!(regs.get(v!(r 3)), Register::RDX);
    assert_eq!(regs.get(v!(r 4)), Register::RAX);
    assert_eq!(regs.get(v!(r 5)), Register::RDX);
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
