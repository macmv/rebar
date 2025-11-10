use std::{
  collections::{BTreeMap, HashMap, HashSet},
  fmt,
};

use rb_codegen::{
  BlockId, Function, Immediate, Instruction, InstructionInput, InstructionOutput, Math, Opcode,
  TVec, TerminatorInstruction, Variable, VariableSize,
};
use rb_codegen_opt::analysis::{Analysis, dominator_tree::DominatorTree, value_uses::ValueUses};
use smallvec::smallvec;

use crate::{Register, RegisterIndex, var_to_reg_size};

#[derive(Default)]
pub struct VariableRegisters {
  registers: TVec<Variable, Register>,
}

trait RegallocDebug {
  fn log_preference(&mut self, var: Variable, reg: RegisterIndex, loc: InstructionLocation) {
    let _ = (var, reg, loc);
  }
}

struct Regalloc<'a, D: RegallocDebug> {
  dom:      &'a DominatorTree,
  function: &'a mut Function,

  state: RegallocState<'a, D>,
}

struct RegallocState<'a, D: RegallocDebug> {
  vu:    &'a ValueUses,
  alloc: &'a mut VariableRegisters,
  debug: &'a mut D,

  active:              HashMap<RegisterIndex, Variable>,
  visited:             HashSet<BlockId>,
  current_instruction: HashSet<Variable>,

  preference: HashMap<Variable, (RegisterIndex, InstructionLocation)>,

  first_new_variable: u32,
  next_variable:      u32,
  copies:             BTreeMap<InstructionLocation, Vec<Move>>,

  rehomes:         HashMap<Variable, Variable>,
  rehomes_reverse: HashMap<Variable, Variable>,
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct InstructionLocation {
  block: BlockId,
  index: usize,
}

enum Move {
  VarReg { from: Variable, to: RegisterIndex },
  VarVar { from: Variable, to: Variable },
  ImmVar { from: Immediate, to: Variable },
}

enum Requirement {
  /// The operand must be in the given register.
  Specific(RegisterIndex),
  /// The operand must in in a register, but it does not matter which.
  Register(VariableSize),
  /// The operand may be in a register or immediate.
  None,
}

impl VariableRegisters {
  pub fn pass(function: &mut Function) -> Self {
    struct NopDebug;

    impl RegallocDebug for NopDebug {}

    Self::pass_debug(function, &mut NopDebug)
  }
  fn pass_debug(function: &mut Function, debug: &mut impl RegallocDebug) -> Self {
    let mut analysis = Analysis::default();
    analysis.load(DominatorTree::ID, function);
    analysis.load(ValueUses::ID, function);

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
    let first_new_variable = last_variable.map(|v| v + 1).unwrap_or(0);

    let mut regs = VariableRegisters::default();
    let mut regalloc = Regalloc {
      dom: analysis.get(),
      function,
      state: RegallocState {
        vu: analysis.get(),
        alloc: &mut regs,
        debug,

        active: HashMap::new(),
        visited: HashSet::new(),
        current_instruction: HashSet::new(),
        preference: HashMap::new(),
        first_new_variable,
        next_variable: first_new_variable,
        copies: BTreeMap::new(),

        rehomes: HashMap::new(),
        rehomes_reverse: HashMap::new(),
      },
    };
    regalloc.pass();

    for (loc, moves) in regalloc.state.copies.iter().rev() {
      let block = regalloc.function.block_mut(loc.block);
      for m in moves.iter().rev() {
        match m {
          Move::VarReg { from, to } => {
            let new_var = Variable::new(regalloc.state.next_variable, from.size());
            regalloc.state.next_variable += 1;

            block.instructions.insert(
              loc.index,
              Instruction {
                opcode: Opcode::Move,
                input:  smallvec![(*from).into()],
                output: smallvec![new_var.into()],
              },
            );
            regalloc.state.alloc.registers.set_with(
              new_var,
              Register { size: var_to_reg_size(new_var.size()).unwrap(), index: *to },
              || Register::RAX,
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

impl<D: RegallocDebug> Regalloc<'_, D> {
  pub fn pass(&mut self) {
    self.pre_allocation();

    let mut live_outs = HashSet::new();

    for (i, arg) in self.function.args().enumerate() {
      let index = match calling_convention(i) {
        Requirement::Specific(reg) => reg,
        _ => unreachable!(),
      };

      self
        .state
        .alloc
        .registers
        .set(arg, Register { size: var_to_reg_size(arg.size()).unwrap(), index });
    }

    for block in self.dom.preorder() {
      self.state.visited.insert(block);
      let live_ins = HashSet::new(); // "set of instructions live into `block`"

      self.state.expire_intervals(&live_ins, &live_outs);
      self.state.start_intervals(block, &live_ins, &live_outs);

      for i in 0..self.function.block(block).instructions.len() {
        let loc = InstructionLocation { block, index: i };
        self.visit_instr(&mut live_outs, loc);

        let instr = &self.function.block(block).instructions[i];

        for (i, out) in instr.output.iter().enumerate() {
          let &InstructionOutput::Var(out) = out;

          let requirement = Requirement::for_output(self, instr, i);

          let used_later = self.is_used_after(InstructionLocation { block, index: i }, out);

          let register = requirement.unwrap_or_else(|| self.state.pick_register(loc, out));

          if used_later {
            self.state.active.insert(register, out);
            live_outs.insert(out);
          }
          self.state.alloc.registers.set_with(
            out,
            Register { size: var_to_reg_size(out.size()).unwrap(), index: register },
            || Register::RAX,
          );
        }
      }

      let loc = InstructionLocation { block, index: self.function.block(block).instructions.len() };
      let args = self.function.sig.args.len();
      if let TerminatorInstruction::Return(ref mut inputs) =
        self.function.block_mut(block).terminator
      {
        for (i, input) in inputs.iter_mut().enumerate() {
          let requirement = calling_convention(args + i);

          if let InstructionInput::Var(v) = input {
            self.state.apply_rehomes(v);
          }

          if let Some(new_var) = self.state.satisfy_requirement(loc, *input, requirement) {
            *input = InstructionInput::Var(new_var);
          }
        }

        for input in inputs {
          if let InstructionInput::Var(v) = input {
            live_outs.remove(&v);
            if !self.state.is_used_later(&[], &TerminatorInstruction::Trap, *v) {
              self.state.free(*v);
            }
          }
        }
      }
    }
  }

  fn pre_allocation(&mut self) {
    for block in self.function.blocks() {
      for (i, instr) in self.function.block(block).instructions.iter().enumerate() {
        let loc = InstructionLocation { block, index: i };
        if !matches!(instr.opcode, Opcode::Syscall | Opcode::Call(_) | Opcode::CallExtern(_)) {
          continue;
        }

        for (i, &input) in instr.input.iter().enumerate() {
          let InstructionInput::Var(var) = input else { continue };

          let reg_index = match (instr.opcode, i) {
            (Opcode::Syscall, 0) => RegisterIndex::Eax,
            (Opcode::Syscall, 1) => RegisterIndex::Edi,
            (Opcode::Syscall, 2) => RegisterIndex::Esi,
            (Opcode::Syscall, 3) => RegisterIndex::Edx,

            (Opcode::Call(_), _) => match calling_convention(i) {
              Requirement::Specific(reg) => reg,
              _ => unreachable!(),
            },

            // TODO: More calling conventions?
            (Opcode::CallExtern(_), 0) => RegisterIndex::Edi,
            (Opcode::CallExtern(_), 1) => RegisterIndex::Esi,
            (Opcode::CallExtern(_), 2) => RegisterIndex::Edx,

            _ => unreachable!(),
          };

          self.state.prefer(var, reg_index, loc);
        }
      }

      if let TerminatorInstruction::Return(ref inputs) = self.function.block(block).terminator {
        for (i, input) in inputs.iter().enumerate() {
          let InstructionInput::Var(var) = input else { continue };

          let reg_index = match calling_convention(self.function.sig.args.len() + i) {
            Requirement::Specific(reg) => reg,
            _ => unreachable!(),
          };

          self.state.prefer(
            *var,
            reg_index,
            InstructionLocation { block, index: self.function.block(block).instructions.len() },
          );
        }
      }
    }
  }

  /// Visiting an instructtion does two things:
  /// - Satisfies register requirements. Some registers may be prefered, but
  ///   variables won't always be allocated to their preference. So, this is
  ///   where we add moves to fix that.
  /// - Move registers we still need that get clobbered.
  fn visit_instr(&mut self, live_outs: &mut HashSet<Variable>, loc: InstructionLocation) {
    let input_len = self.function.block(loc.block).instructions[loc.index].input.len();
    for i in 0..input_len {
      let instr = &mut self.function.block_mut(loc.block).instructions[loc.index];
      let requirement = Requirement::for_input(instr, i);
      let input = &mut instr.input[i];

      if let InstructionInput::Var(v) = input {
        self.state.apply_rehomes(v);
      }

      if let Some(new_var) = self.state.satisfy_requirement(loc, *input, requirement) {
        *input = InstructionInput::Var(new_var);
        self.state.active.insert(self.state.alloc.registers.get(new_var).unwrap().index, new_var);
        self.state.current_instruction.insert(new_var);
      } else {
        match input {
          InstructionInput::Var(v) => {
            let reg = self.state.alloc.registers.get(*v).unwrap().index;
            self.state.active.insert(reg, *v);
            self.state.current_instruction.insert(*v);
          }
          _ => {}
        }
      }
    }

    let instr = &self.function.block(loc.block).instructions[loc.index];
    for input in instr.input.clone() {
      if let InstructionInput::Var(v) = input {
        live_outs.remove(&v);
        if !self.is_used_after(loc, v) {
          self.state.free(v);
        }
      }
    }

    self.state.current_instruction.clear();

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
        self.clobber(var);
      }
    }
    */
  }

  fn is_used_after(&self, loc: InstructionLocation, var: Variable) -> bool {
    let block = self.function.block(loc.block);
    self.state.is_used_later(&block.instructions[loc.index + 1..], &block.terminator, var)
  }
}

impl<D: RegallocDebug> RegallocState<'_, D> {
  fn expire_intervals(&mut self, live_ins: &HashSet<Variable>, live_outs: &HashSet<Variable>) {
    for &var in live_outs.iter().filter(|&&v| !live_ins.contains(&v)) {
      self.free(var);
    }
  }

  fn start_intervals(
    &mut self,
    block: BlockId,
    live_ins: &HashSet<Variable>,
    live_outs: &HashSet<Variable>,
  ) {
    let loc = InstructionLocation { block, index: 0 };
    for &var in live_ins.iter().filter(|&&v| !live_outs.contains(&v)) {
      self.allocate(loc, var);
    }
  }

  fn satisfy_requirement(
    &mut self,
    loc: InstructionLocation,
    input: InstructionInput,
    requirement: Requirement,
  ) -> Option<Variable> {
    let (requirement, prev) = match requirement {
      Requirement::None => return None,
      Requirement::Register(size) => {
        let new_var = self.fresh_var(size);
        let reg = self.pick_register(loc, new_var);
        (reg, self.active.get(&reg).copied())
      }
      Requirement::Specific(reg) => (reg, self.active.get(&reg).copied()),
    };

    let mut moves = vec![];

    let new_var = match input {
      InstructionInput::Var(v) => match prev {
        Some(active) if active == v => None,
        Some(other) => {
          moves.push(Move::VarReg { from: other, to: RegisterIndex::Ebx });

          let new_var = self.fresh_var(v.size());
          moves.push(Move::VarVar { from: v, to: new_var });
          self.alloc.registers.set_with(
            new_var,
            Register { size: var_to_reg_size(v.size()).unwrap(), index: requirement },
            || Register::RAX,
          );
          Some(new_var)
        }
        None => {
          if self.alloc.registers.get(v).is_some_and(|r| r.index != requirement) {
            let new_var = self.fresh_var(v.size());
            moves.push(Move::VarVar { from: v, to: new_var });
            self.alloc.registers.set_with(
              new_var,
              Register { size: var_to_reg_size(v.size()).unwrap(), index: requirement },
              || Register::RAX,
            );
            Some(new_var)
          } else {
            None
          }
        }
      },
      InstructionInput::Imm(imm) => match prev {
        Some(other) => {
          self.rehome(loc, other);

          let new_var = self.fresh_var(VariableSize::Bit64);
          moves.push(Move::ImmVar { from: imm, to: new_var });
          self.alloc.registers.set_with(
            new_var,
            Register { size: var_to_reg_size(VariableSize::Bit64).unwrap(), index: requirement },
            || Register::RAX,
          );
          Some(new_var)
        }
        None => {
          let new_var = self.fresh_var(VariableSize::Bit64);
          moves.push(Move::ImmVar { from: imm, to: new_var });
          self.alloc.registers.set_with(
            new_var,
            Register { size: var_to_reg_size(VariableSize::Bit64).unwrap(), index: requirement },
            || Register::RAX,
          );
          Some(new_var)
        }
      },
    };

    self.copies.entry(loc).or_default().extend(moves);

    new_var
  }

  fn fresh_var(&mut self, size: VariableSize) -> Variable {
    let v = Variable::new(self.next_variable, size);
    self.next_variable += 1;
    v
  }

  fn allocate(&mut self, loc: InstructionLocation, var: Variable) {
    let reg = self.pick_register(loc, var);
    self.active.insert(reg, var);
    self.alloc.registers.set_with(
      var,
      Register { size: var_to_reg_size(var.size()).unwrap(), index: reg },
      || Register::RAX,
    );
  }

  fn free(&mut self, var: Variable) {
    if let Some((&reg, _)) = self.active.iter().find(|&(_, &v)| v == var) {
      self.active.remove(&reg);
    }
  }

  fn pick_register(&mut self, loc: InstructionLocation, var: Variable) -> RegisterIndex {
    if let Some(pref) = self.preference_after(loc, var) {
      match self.active.get(&pref) {
        // If the variable is already in the preferred register, or there is nothing in the
        // preferred register, use that.
        Some(&other) if other == var => return pref,
        None => return pref,

        Some(&other) if self.current_instruction.contains(&other) => {}
        Some(&other) => {
          self.rehome(loc, other);
          self.active.remove(&pref);

          return pref;
        }
      }
    }

    for reg_index in 0..8 {
      let reg_index = RegisterIndex::from_usize(reg_index);

      if !self.active.contains_key(&reg_index) {
        return reg_index;
      }
    }

    panic!("no registers available for variable {var:?}");
  }

  fn rehome(&mut self, loc: InstructionLocation, var: Variable) {
    let new_var = self.fresh_var(var.size());
    let new_reg = self.pick_register(loc, var);
    self.alloc.registers.set_with(
      new_var,
      Register { size: var_to_reg_size(var.size()).unwrap(), index: new_reg },
      || Register::RAX,
    );
    self.active.insert(new_reg, new_var);

    self.copies.entry(loc).or_default().push(Move::VarVar { from: var, to: new_var });
    self.rehomes.insert(var, new_var);
    self.rehomes_reverse.insert(new_var, var);
  }

  fn apply_rehomes(&mut self, v: &mut Variable) {
    while let Some(&new_v) = self.rehomes.get(v) {
      *v = new_v;
    }
  }

  fn preference_after(&self, loc: InstructionLocation, var: Variable) -> Option<RegisterIndex> {
    if let Some(&(pref, pref_loc)) = self.preference.get(&var) {
      if pref_loc >= loc {
        return Some(pref);
      }
    }

    None
  }

  fn is_used_later(
    &self,
    after: &[Instruction],
    term: &TerminatorInstruction,
    var: Variable,
  ) -> bool {
    if self.is_tmp_var(var) {
      return false;
    }

    let is_used_in_later_block = self
      .vu
      .variable(var)
      .used_by
      .iter()
      .any(|u| !self.visited.contains(&self.vu.variables_to_block[u]));
    let is_used_later_by_term = match term {
      TerminatorInstruction::Return(inputs) => inputs.iter().any(|input| match input {
        InstructionInput::Var(v) => *v == var,
        _ => false,
      }),
      _ => false,
    };
    let is_used_in_block = is_used_later_in_block(after, var);

    is_used_in_later_block || is_used_later_by_term || is_used_in_block
  }

  fn is_tmp_var(&self, var: Variable) -> bool { var.id() >= self.first_new_variable }

  fn prefer(&mut self, var: Variable, reg_index: RegisterIndex, loc: InstructionLocation) {
    match self.preference.entry(var) {
      std::collections::hash_map::Entry::Occupied(_) => {}
      std::collections::hash_map::Entry::Vacant(entry) => {
        self.debug.log_preference(var, reg_index, loc);
        entry.insert((reg_index, loc));
      }
    }
  }
}

fn calling_convention(index: usize) -> Requirement {
  match index {
    0 => Requirement::Specific(RegisterIndex::Edi),
    1 => Requirement::Specific(RegisterIndex::Esi),
    2 => Requirement::Specific(RegisterIndex::Edx),
    3 => Requirement::Specific(RegisterIndex::Ebx),
    4 => Requirement::Specific(RegisterIndex::Ecx),
    _ => todo!("more arguments"),
  }
}

impl Requirement {
  fn for_input(instr: &Instruction, index: usize) -> Requirement {
    use Requirement::*;

    match instr.opcode {
      Opcode::Syscall => match index {
        0 => Specific(RegisterIndex::Eax),
        1 => Specific(RegisterIndex::Edi),
        2 => Specific(RegisterIndex::Esi),
        3 => Specific(RegisterIndex::Edx),
        _ => unreachable!(),
      },
      Opcode::Call(_) => calling_convention(index),
      Opcode::CallExtern(_) => match index {
        0 => Specific(RegisterIndex::Edi),
        1 => Specific(RegisterIndex::Esi),
        2 => Specific(RegisterIndex::Edx),
        _ => todo!("more arguments"),
      },
      Opcode::Math(_) => {
        if index == 0 {
          Specific(RegisterIndex::Eax)
        } else {
          Register(instr.input[0].unwrap_var().size())
        }
      }
      _ => None,
    }
  }

  fn for_output<D: RegallocDebug>(
    regalloc: &Regalloc<D>,
    instr: &Instruction,
    index: usize,
  ) -> Option<RegisterIndex> {
    match instr.opcode {
      Opcode::Math(m) => {
        let InstructionInput::Var(v) = instr.input[0] else {
          panic!("expected var input for math instruction: {instr}");
        };
        let input = regalloc.state.alloc.registers.get(v).unwrap();

        match m {
          // In-place, any register.
          Math::Add
          | Math::Sub
          | Math::And
          | Math::Or
          | Math::Xor
          | Math::Not
          | Math::Neg
          | Math::Shl
          | Math::Ishr
          | Math::Ushr => Some(input.index),
          // In-place, only EAX.
          Math::Imul | Math::Umul | Math::Idiv | Math::Udiv => Some(RegisterIndex::Eax),
          // In-place, only EDX.
          Math::Irem | Math::Urem => Some(RegisterIndex::Edx),
        }
      }
      Opcode::Call(_) => Some(match calling_convention(instr.input.len() + index) {
        Requirement::Specific(reg) => reg,
        _ => unreachable!(),
      }),
      Opcode::CallExtern(_) => match index {
        0 => Some(RegisterIndex::Eax),
        _ => unreachable!("call with more than 1 return"),
      },
      Opcode::Syscall => match index {
        0 => Some(RegisterIndex::Eax),
        _ => unreachable!("syscalls only have 1 output"),
      },
      _ => None,
    }
  }
}

fn is_used_later_in_block(after: &[Instruction], var: Variable) -> bool {
  for instr in after.iter() {
    for input in &instr.input {
      if let InstructionInput::Var(v) = input
        && *v == var
      {
        return true;
      }
    }
  }

  false
}

impl fmt::Display for InstructionLocation {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "<{}, instr {}>", self.block, self.index)
  }
}

#[cfg(test)]
mod tests {
  use rb_codegen_opt::{VariableDisplay, parse};
  use rb_test::{Expect, expect};

  use crate::regalloc::{RegallocDebug, VariableRegisters};

  impl VariableDisplay for VariableRegisters {
    fn write_variable(
      &self,
      f: &mut std::fmt::Formatter,
      var: rb_codegen::Variable,
    ) -> std::fmt::Result {
      write!(f, "{}({})", self.get(var), var.id())
    }
  }

  fn check(function: &str, expected: Expect) {
    let mut function = parse(function);
    let regs = VariableRegisters::pass(&mut function.function);
    function.check_annotated(expected, &regs);
  }

  struct Debug {
    out: String,
  }

  impl RegallocDebug for Debug {
    fn log_preference(
      &mut self,
      var: rb_codegen::Variable,
      reg: crate::RegisterIndex,
      loc: super::InstructionLocation,
    ) {
      self.out.push_str(&format!("preference: {var} -> {reg:?} at {loc}\n"));
    }
  }

  fn check_v(function: &str, expected: Expect) {
    let mut function = parse(function);
    let mut debug = Debug { out: String::new() };
    let regs = VariableRegisters::pass_debug(&mut function.function, &mut debug);

    let func = function.annotate(&regs);
    expected.assert_eq(&format!("{}\n{}", debug.out, func));
  }

  #[test]
  fn simple_syscall() {
    check(
      "
      block 0:
        mov r0 = 0x01
        mov r1 = 0x00
        syscall r2 = r0, r1
        mov r3 = 0x02
        syscall r4 = r0, r3
        mov r5 = 0x03
        syscall r6 = r5, r1
      ",
      expect![@r#"
        block 0:
          mov rax(0) = 0x01
          mov rdi(1) = 0x00
          syscall rax(2) = rax(0), rdi(1)
          mov rcx(7) = rdi(1)
          mov rdi(3) = 0x02
          syscall rax(4) = rax(0), rdi(3)
          mov rax(5) = 0x03
          mov rdi(8) = rcx(7)
          syscall rax(6) = rax(5), rdi(8)
          trap
      "#
      ],
    );
  }

  #[test]
  fn syscall_with_imm() {
    check(
      "
      block 0:
        syscall r0 = 0x00, 0x01
        syscall r1 = 0x00, 0x02
        syscall r2 = 0x00, 0x03
      ",
      expect![@r#"
        block 0:
          mov rax(3) = 0x00
          mov rdi(4) = 0x01
          syscall rax(0) = rax(3), rdi(4)
          mov rax(5) = 0x00
          mov rdi(6) = 0x02
          syscall rax(1) = rax(5), rdi(6)
          mov rax(7) = 0x00
          mov rdi(8) = 0x03
          syscall rax(2) = rax(7), rdi(8)
          trap
      "#
      ],
    );
  }

  #[test]
  fn call_with_imm() {
    check(
      "
      block 0:
        call foo r0 = 0x00, 0x01
      ",
      expect![@r#"
        block 0:
          mov rdi(1) = 0x00
          mov rsi(2) = 0x01
          call function 0 rdx(0) = rdi(1), rsi(2)
          trap
      "#
      ],
    );
  }

  #[test]
  fn call_imul() {
    check(
      "
      block 0:
        math(imul) r0 = 0x02, 0x03
        return r0
      ",
      expect![@r#"
        block 0:
          mov rax(1) = 0x02
          mov rcx(3) = 0x03
          math(imul) rax(0) = rax(1), rcx(3)
          mov rdi(4) = rax(0)
          return r4
      "#
      ],
    );
  }

  #[test]
  fn multi_return() {
    check(
      "
      block 0:
        call 0 r0, r1 =
        call 0 = r0, 0x01
        call 0 = r1, 0x02
        trap
      ",
      expect![@r#"
        block 0:
          call function 0 rdi(0), rsi(1) =
          mov rax(2) = rsi(1)
          mov rsi(3) = 0x01
          call function 0 = rdi(0), rsi(3)
          mov rdi(4) = rax(2)
          mov rsi(5) = 0x02
          call function 0 = rdi(4), rsi(5)
          trap
      "#
      ],
    );
  }

  #[test]
  fn save_registers() {
    check_v(
      "
      block 0:
        mov r0 = 0x01
        call 0 = 0x02
        return r0
      ",
      expect![@r#"
        preference: r0 -> Edi at <block 0, instr 2>

        block 0:
          mov rdi(0) = 0x01
          mov rdi(1) = rdi(0)
          mov rdi(2) = 0x02
          call function 0 = rdi(2)
          return r1
      "#
      ],
    );
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
