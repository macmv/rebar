use std::{
  collections::{BTreeSet, HashMap, HashSet},
  fmt,
  ops::Range,
};

use rb_codegen::{
  BlockId, Function, Instruction, InstructionInput, InstructionOutput, Math, Opcode, StackId,
  StackSlot, TVec, TerminatorInstruction, Variable, VariableSize,
};
use rb_codegen_opt::analysis::{Analysis, dominator_tree::DominatorTree, value_uses::ValueUses};
use smallvec::smallvec;

use crate::{Register, RegisterIndex, RegisterSize, var_to_reg_size};

#[derive(Default)]
pub struct VariableRegisters {
  registers: TVec<Variable, Option<RegisterSpill>>,
  saved:     RegisterMap<bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegisterSpill {
  Register(Register),
  Spill(StackId, RegisterSize),
}

trait RegallocDebug {
  fn log(&mut self, msg: fmt::Arguments) { let _ = msg; }
}

struct NopDebug;

impl RegallocDebug for NopDebug {}

#[derive(Clone, Copy)]
struct RegisterMap<T> {
  values: [Option<T>; RegisterIndex::COUNT],
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct InstructionIndex(usize);

#[derive(Debug, Default)]
enum Requirement {
  /// The operand must be in the given register.
  Specific(RegisterIndex),
  /// The operand must in in a register, but it does not matter which.
  Register,
  /// Only applicable to outputs: the output register must be the same as the
  /// first argument.
  InPlace,
  /// The operand may be in a register or immediate.
  #[default]
  None,
}

#[derive(Default)]
struct LiveIntervals {
  intervals: HashMap<Variable, Interval>,
  calls:     BTreeSet<InstructionIndex>,
}

#[derive(Debug, Default)]
struct Interval {
  segments:    Vec<Range<InstructionIndex>>,
  assigned:    Option<RegisterIndex>,
  must_match:  Option<Variable>,
  requirement: Requirement,
}

impl VariableRegisters {
  pub fn pass(function: &mut Function) -> Self { Self::pass_debug(function, &mut NopDebug) }

  pub fn saved(&self) -> impl Iterator<Item = RegisterIndex> {
    self.saved.iter().filter_map(|(reg, &saved)| if saved { Some(reg) } else { None })
  }

  fn pass_debug(
    function: &mut Function,
    #[cfg(not(debug_assertions))] debug: &mut NopDebug,
    #[cfg(debug_assertions)] debug: &mut dyn RegallocDebug,
  ) -> Self {
    let mut analysis = Analysis::default();
    analysis.load(DominatorTree::ID, function);
    analysis.load(ValueUses::ID, function);

    imm_to_reg(function);
    split_critical_variables(function);

    let mut intervals = live_intervals(function);

    let mut regs = VariableRegisters::default();
    let sorted = intervals.sorted();

    let mut active = HashSet::new();
    for var in sorted {
      let interval = intervals.for_var(var);

      #[cfg(debug_assertions)]
      let mut expired = BTreeSet::new();

      let current_start = interval.segments.first().unwrap().start;
      active.retain(|active_var| {
        let active_interval = &intervals.for_var(*active_var);

        let active_end = active_interval.segments.last().unwrap().end;

        if active_end.0 <= current_start.0 + 1 {
          #[cfg(debug_assertions)]
          expired.insert(*active_var);
          false
        } else {
          true
        }
      });

      #[cfg(debug_assertions)]
      for expired in expired {
        debug.log(format_args!("expiring {expired} at {current_start:?}",));
      }

      debug.log(format_args!("activating {var} at {:?}", interval.segments.first().unwrap().start));

      if let Some(v) = interval.must_match {
        if let Some(index) = intervals.for_var(v).assigned {
          active.insert(var);

          regs.registers.set_default(
            var,
            Some(RegisterSpill::Register(Register {
              index: index,
              size:  var_to_reg_size(var.size()).unwrap(),
            })),
          );

          continue;
        } else {
          panic!("cannot assign in-place requirement for variable {var} to match {v}");
        }
      }

      if let Some(reg_index) = interval.assigned {
        if active.iter().all(|active_var| {
          let active_interval = intervals.for_var(*active_var);
          active_interval.assigned != Some(reg_index)
        }) {
          active.insert(var);

          regs.registers.set_default(
            var,
            Some(RegisterSpill::Register(Register {
              index: reg_index,
              size:  var_to_reg_size(var.size()).unwrap(),
            })),
          );
        } else if interval.requirement.is_none() {
          active.insert(var);

          let slot = StackId(function.stack_slots.len() as u32);
          function.stack_slots.push(StackSlot {
            offset: 0,
            size:   var.size().bytes(),
            align:  var.size().bytes(),
          });

          regs.registers.set_default(
            var,
            Some(RegisterSpill::Spill(slot, var_to_reg_size(var.size()).unwrap())),
          );
        } else if let Some(active_var) = active
          .iter()
          .find(|active_var| {
            let active_interval = intervals.for_var(**active_var);
            active_interval.assigned == Some(reg_index)
          })
          .copied()
        {
          // spill `active_var` to stack
          active.insert(var);
          debug.log(format_args!("spilling {active_var} to assign {var} = {reg_index:?}",));

          let slot = StackId(function.stack_slots.len() as u32);
          function.stack_slots.push(StackSlot {
            offset: 0,
            size:   active_var.size().bytes(),
            align:  active_var.size().bytes(),
          });

          regs.registers.set_default(
            active_var,
            Some(RegisterSpill::Spill(slot, var_to_reg_size(var.size()).unwrap())),
          );

          regs.registers.set_default(
            var,
            Some(RegisterSpill::Register(Register {
              index: reg_index,
              size:  var_to_reg_size(var.size()).unwrap(),
            })),
          );
        } else {
          panic!("cannot assign required register {:?} to variable {:?}", reg_index, var);
        }
      } else {
        active.insert(var);

        let choices =
          if intervals.calls.range(interval.segments.first().unwrap().clone()).next().is_some() {
            SAVED
          } else {
            RegisterIndex::all()
          };

        for reg_index in choices {
          if active.iter().all(|active_var| {
            let active_interval = intervals.for_var(*active_var);
            active_interval.assigned != Some(*reg_index)
          }) {
            intervals.assign(var, *reg_index);
            regs.registers.set_default(
              var,
              Some(RegisterSpill::Register(Register {
                index: *reg_index,
                size:  var_to_reg_size(var.size()).unwrap(),
              })),
            );
            break;
          }
        }
      }
    }

    fix_requirements(function, &mut regs);

    regs
  }

  #[track_caller]
  pub fn get(&self, var: Variable) -> RegisterSpill {
    match self.registers.get(var) {
      Some(Some(reg)) => *reg,

      _ => panic!("variable {var:?} is not in a register"),
    }
  }
}

struct FunctionEditor<'a> {
  function:    &'a mut Function,
  next_var_id: u32,
}

struct FunctionChange<'a, 'b: 'a> {
  editor: &'a mut FunctionEditor<'b>,

  block: BlockId,
  instr: usize,
}

impl<'a> FunctionEditor<'a> {
  pub fn new(function: &'a mut Function) -> Self {
    let next_var_id = function
      .blocks()
      .flat_map(|b| function.block(b).instructions.iter())
      .flat_map(|instr| {
        instr
          .input
          .iter()
          .filter_map(|i| match i {
            InstructionInput::Var(v) => Some(*v),
            _ => None,
          })
          .chain(instr.output.iter().filter_map(|o| match o {
            InstructionOutput::Var(v) => Some(*v),
          }))
      })
      .max_by_key(|v| v.id())
      .map_or(0, |id| id.id() + 1);

    FunctionEditor { function, next_var_id }
  }

  pub fn fresh_var(&mut self, size: VariableSize) -> Variable {
    let var = Variable::new(self.next_var_id, size);
    self.next_var_id += 1;
    var
  }

  pub fn edit(
    &mut self,
    mut f: impl FnMut(&mut FunctionChange, &mut Instruction),
    mut t: impl FnMut(&mut FunctionChange, &mut TerminatorInstruction),
  ) {
    self.edit_context(
      &mut (),
      |(), change, instr| f(change, instr),
      |(), change, term| t(change, term),
    );
  }

  pub fn edit_context<T>(
    &mut self,
    context: &mut T,
    mut f: impl FnMut(&mut T, &mut FunctionChange, &mut Instruction),
    mut t: impl FnMut(&mut T, &mut FunctionChange, &mut TerminatorInstruction),
  ) {
    for block_id in self.function.blocks() {
      let mut i = 0;
      while i < self.function.block(block_id).instructions.len() {
        let mut instr = self.function.block(block_id).instructions[i].clone();

        let mut change = FunctionChange { editor: self, block: block_id, instr: i };
        f(context, &mut change, &mut instr);

        i = change.instr;
        self.function.block_mut(block_id).instructions[i] = instr;
        i += 1;
      }

      let mut terminator = self.function.block(block_id).terminator.clone();
      let mut change = FunctionChange { editor: self, block: block_id, instr: i };
      t(context, &mut change, &mut terminator);
      self.function.block_mut(block_id).terminator = terminator;
    }
  }
}

impl FunctionChange<'_, '_> {
  fn insert(&mut self, instr: Instruction) {
    let block = self.editor.function.block_mut(self.block);
    block.instructions.insert(self.instr, instr);
    self.instr += 1;
  }
}

fn split_critical_variables(function: &mut Function) {
  let mut specific_defs = HashMap::<Variable, RegisterIndex>::new();

  for (i, size) in function.sig.args.iter().enumerate() {
    let req = calling_convention(i);

    specific_defs.insert(
      Variable::new(i as u32, *size),
      match req {
        Requirement::Specific(reg) => reg,
        _ => unreachable!(),
      },
    );
  }

  FunctionEditor::new(function).edit_context(
    &mut specific_defs,
    |specific_defs, change, instr| {
      for j in 0..instr.input.len() {
        let req = Requirement::for_input(&instr, j);
        let input = &mut instr.input[j];

        match (*input, req) {
          (InstructionInput::Var(v), Requirement::Specific(req))
            if specific_defs.get(&v).is_some_and(|def| *def != req) =>
          {
            let prev_input = input.clone();
            let tmp = change.editor.fresh_var(VariableSize::Bit64);
            *input = InstructionInput::Var(tmp);

            change.insert(Instruction {
              opcode: Opcode::Move,
              input:  smallvec![prev_input],
              output: smallvec![tmp.into()],
            });
          }
          _ => continue,
        }
      }

      for j in 0..instr.output.len() {
        let req = Requirement::for_output(&instr, j);
        let output = &instr.output[j];

        match (*output, req) {
          (InstructionOutput::Var(v), Requirement::Specific(req)) => {
            specific_defs.insert(v, req);
          }
          _ => {}
        }
      }
    },
    |specific_defs, change, term| match term {
      TerminatorInstruction::Return(rets) => {
        for j in 0..rets.len() {
          let req = Requirement::for_terminator(&TerminatorInstruction::Return(rets.clone()), j);
          let input = &mut rets[j];

          match (*input, req) {
            (InstructionInput::Var(v), Requirement::Specific(req))
              if specific_defs.get(&v).is_some_and(|def| *def != req) =>
            {
              let prev_input = input.clone();
              let tmp = change.editor.fresh_var(VariableSize::Bit64);

              *input = InstructionInput::Var(tmp);
              change.insert(Instruction {
                opcode: Opcode::Move,
                input:  smallvec![prev_input],
                output: smallvec![tmp.into()],
              });
            }
            _ => continue,
          }
        }
      }
      _ => {}
    },
  );
}

fn imm_to_reg(function: &mut Function) {
  FunctionEditor::new(function).edit(
    |change, instr| {
      for i in 0..instr.input.len() {
        let req = Requirement::for_input(&instr, i);
        let input = &mut instr.input[i];

        match (*input, req) {
          (_, Requirement::None) => continue,
          (InstructionInput::Var(_), _) => continue,
          (InstructionInput::Imm(_), _) => {
            let prev_input = input.clone();
            let tmp = change.editor.fresh_var(VariableSize::Bit64);
            *input = InstructionInput::Var(tmp);

            change.insert(Instruction {
              opcode: Opcode::Move,
              input:  smallvec![prev_input],
              output: smallvec![tmp.into()],
            });
          }
        }
      }
    },
    |change, term| match term {
      TerminatorInstruction::Return(rets) => {
        for i in 0..rets.len() {
          let req = Requirement::for_terminator(&term, i);
          let input = match term {
            TerminatorInstruction::Return(rets) => &mut rets[i],
            _ => unreachable!(),
          };

          match (*input, req) {
            (_, Requirement::None) => continue,
            (InstructionInput::Var(_), _) => continue,
            (InstructionInput::Imm(_), _) => {
              let prev_input = input.clone();
              let tmp = change.editor.fresh_var(VariableSize::Bit64);
              *input = InstructionInput::Var(tmp);

              change.insert(Instruction {
                opcode: Opcode::Move,
                input:  smallvec![prev_input],
                output: smallvec![tmp.into()],
              });
            }
          }
        }
      }
      _ => {}
    },
  );
}

fn fix_requirements(function: &mut Function, regs: &mut VariableRegisters) {
  FunctionEditor::new(function).edit_context(
    regs,
    |regs, change, instr| {
      for j in 0..instr.input.len() {
        let req = Requirement::for_input(&instr, j);
        match req {
          Requirement::None => continue,
          _ => {}
        }

        let input = &mut instr.input[j];

        match input {
          InstructionInput::Var(v) => {
            if regs.get(*v).is_spill() {
              let copy = change.editor.fresh_var(v.size());

              regs.registers.set_default(
                copy,
                Some(RegisterSpill::Register(Register {
                  index: match req {
                    Requirement::Specific(reg) => reg,
                    // TODO
                    Requirement::Register => RegisterIndex::Eax,
                    Requirement::InPlace => todo!("in-place requirements"),
                    Requirement::None => unreachable!(),
                  },
                  size:  var_to_reg_size(v.size()).unwrap(),
                })),
              );
              change.insert(Instruction {
                opcode: Opcode::Move,
                input:  smallvec![InstructionInput::Var(*v)],
                output: smallvec![InstructionOutput::Var(copy)],
              });
              *v = copy;
            }
          }
          InstructionInput::Imm(_) => continue,
        }
      }
    },
    |regs, change, term| match term {
      TerminatorInstruction::Return(rets) => {
        for i in 0..rets.len() {
          let req = Requirement::for_terminator(&term, i);
          match req {
            Requirement::None => continue,
            _ => {}
          }

          let input = match term {
            TerminatorInstruction::Return(rets) => &mut rets[i],
            _ => unreachable!(),
          };

          match input {
            InstructionInput::Var(v) => {
              if regs.get(*v).is_spill() {
                let copy = change.editor.fresh_var(v.size());

                regs.registers.set_default(
                  copy,
                  Some(RegisterSpill::Register(Register {
                    index: match req {
                      Requirement::Specific(reg) => reg,
                      Requirement::Register => {
                        panic!("spilled slot cannot have a register requirement")
                      }
                      Requirement::InPlace => todo!("in-place requirements"),
                      Requirement::None => unreachable!(),
                    },
                    size:  var_to_reg_size(v.size()).unwrap(),
                  })),
                );
                change.insert(Instruction {
                  opcode: Opcode::Move,
                  input:  smallvec![InstructionInput::Var(*v)],
                  output: smallvec![InstructionOutput::Var(copy)],
                });
                *v = copy;
              }
            }
            InstructionInput::Imm(_) => continue,
          }
        }
      }
      _ => {}
    },
  );
}

fn live_intervals(function: &Function) -> LiveIntervals {
  let mut intervals = LiveIntervals::default();

  for (i, size) in function.sig.args.iter().enumerate() {
    let req = calling_convention(i);

    intervals.intervals.insert(
      Variable::new(i as u32, *size),
      Interval {
        segments:    vec![Range { start: InstructionIndex(0), end: InstructionIndex(0) }],
        assigned:    Some(match req {
          Requirement::Specific(reg) => reg,
          _ => unreachable!(),
        }),
        must_match:  None,
        requirement: req,
      },
    );
  }

  // TODO: Value-uses and dominator tree, but this'll work for now.
  let mut i = 0;
  for block in function.blocks() {
    let block = function.block(block);
    for instr in block.instructions.iter() {
      let index = InstructionIndex(i);

      match instr.opcode {
        Opcode::Call(_) | Opcode::CallExtern(_) | Opcode::Syscall => {
          intervals.calls.insert(index);
        }
        _ => {}
      }

      for (j, input) in instr.input.iter().enumerate() {
        if let InstructionInput::Var(v) = input {
          let interval = intervals.intervals.entry(*v).or_default();

          if let Some(last) = interval.segments.last_mut() {
            last.end = InstructionIndex(index.0 + 1);
          }

          interval.requirement = Requirement::for_input(instr, j);
          match interval.requirement {
            Requirement::Specific(reg) => {
              interval.assigned = Some(reg);
            }
            Requirement::InPlace => unreachable!("in-place requirements not allowed for inputs"),
            _ => {}
          }
        }
      }

      for (j, output) in instr.output.iter().enumerate() {
        let InstructionOutput::Var(v) = output;
        let interval = intervals.intervals.entry(*v).or_default();

        if interval.segments.is_empty() {
          interval.segments.push(Range { start: index, end: index });
        }

        interval.requirement = Requirement::for_output(instr, j);
        match interval.requirement {
          Requirement::Specific(reg) => {
            interval.assigned = Some(reg);
          }
          Requirement::InPlace => {
            interval.must_match = Some(match instr.input[0] {
              InstructionInput::Var(v) => v,
              _ => unreachable!("in-place requirements must have variable input"),
            });
          }
          _ => {}
        }
      }

      i += 1;
    }

    let index = InstructionIndex(i);

    match &block.terminator {
      TerminatorInstruction::Return(rets) => {
        for (j, arg) in rets.iter().enumerate() {
          if let InstructionInput::Var(v) = arg {
            let interval = intervals.intervals.entry(*v).or_default();

            if let Some(last) = interval.segments.last_mut() {
              last.end = InstructionIndex(index.0 + 1);
            }

            match Requirement::for_terminator(&block.terminator, j) {
              Requirement::Specific(reg) => {
                interval.assigned = Some(reg);
              }
              _ => {}
            }
          }
        }
      }
      _ => {}
    }
    i += 1;
  }

  intervals
}

impl LiveIntervals {
  pub fn sorted(&self) -> Vec<Variable> {
    let mut sorted = self.intervals.iter().map(|(v, _)| *v).collect::<Vec<Variable>>();
    sorted.sort_unstable_by_key(|v| self.for_var(*v).segments.first().unwrap().start);
    sorted
  }

  pub fn assign(&mut self, var: Variable, reg: RegisterIndex) {
    self.intervals.get_mut(&var).unwrap().assigned = Some(reg);
  }

  pub fn for_var(&self, var: Variable) -> &Interval { self.intervals.get(&var).unwrap() }
}

const SAVED: &[RegisterIndex] = &[
  RegisterIndex::Ebx,
  RegisterIndex::Ebp,
  RegisterIndex::R12,
  RegisterIndex::R13,
  RegisterIndex::R14,
  RegisterIndex::R15,
];

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
  pub fn is_none(&self) -> bool { matches!(self, Requirement::None) }

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
      Opcode::Math(Math::Imul | Math::Umul | Math::Idiv | Math::Udiv | Math::Irem | Math::Urem) => {
        Specific(RegisterIndex::Eax)
      }
      Opcode::Math(_) => {
        if index == 0 {
          Register
        } else {
          None
        }
      }
      _ => None,
    }
  }

  fn for_output(instr: &Instruction, index: usize) -> Requirement {
    use Requirement::*;

    match instr.opcode {
      Opcode::Math(m) => {
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
          | Math::Ushr => InPlace,
          // In-place, only EAX.
          Math::Imul | Math::Umul | Math::Idiv | Math::Udiv => Specific(RegisterIndex::Eax),
          // In-place, only EDX.
          Math::Irem | Math::Urem => Specific(RegisterIndex::Edx),
        }
      }
      Opcode::Call(_) => calling_convention(instr.input.len() + index),
      Opcode::CallExtern(_) => match index {
        0 => Specific(RegisterIndex::Eax),
        _ => unreachable!("call with more than 1 return"),
      },
      Opcode::Syscall => match index {
        0 => Specific(RegisterIndex::Eax),
        _ => unreachable!("syscalls only have 1 output"),
      },
      _ => None,
    }
  }

  fn for_terminator(term: &TerminatorInstruction, index: usize) -> Requirement {
    use Requirement::*;

    match term {
      TerminatorInstruction::Return(_) => calling_convention(index),
      _ => None,
    }
  }
}

impl<T> Default for RegisterMap<T> {
  fn default() -> Self { Self::new() }
}

#[allow(dead_code)]
impl<T> RegisterMap<T> {
  pub fn new() -> Self { Self { values: [(); RegisterIndex::COUNT].map(|_| None) } }

  pub fn get(&self, reg: RegisterIndex) -> Option<&T> { self.values[reg as usize].as_ref() }
  pub fn set(&mut self, reg: RegisterIndex, value: T) { self.values[reg as usize] = Some(value); }
  pub fn remove(&mut self, reg: RegisterIndex) -> Option<T> { self.values[reg as usize].take() }
  pub fn contains(&self, reg: RegisterIndex) -> bool { self.values[reg as usize].is_some() }

  pub fn iter(&self) -> impl Iterator<Item = (RegisterIndex, &T)> {
    self
      .values
      .iter()
      .enumerate()
      .filter_map(|(i, v)| v.as_ref().map(|val| (RegisterIndex::from_usize(i), val)))
  }
}

impl RegisterSpill {
  pub fn size(&self) -> RegisterSize {
    match self {
      RegisterSpill::Register(reg) => reg.size,
      RegisterSpill::Spill(_, size) => *size,
    }
  }

  pub fn is_register(&self) -> bool { matches!(self, RegisterSpill::Register(_)) }
  pub fn is_spill(&self) -> bool { matches!(self, RegisterSpill::Spill(_, _)) }

  pub fn is_register_and(&self, f: impl Fn(Register) -> bool) -> bool {
    match self {
      RegisterSpill::Register(reg) => f(*reg),
      RegisterSpill::Spill(_, _) => false,
    }
  }

  #[track_caller]
  pub fn unwrap_register(&self) -> Register {
    match self {
      RegisterSpill::Register(reg) => *reg,
      RegisterSpill::Spill(_, _) => panic!("not a register"),
    }
  }
}

impl PartialEq<Register> for RegisterSpill {
  fn eq(&self, other: &Register) -> bool {
    match self {
      RegisterSpill::Register(reg) => reg == other,
      RegisterSpill::Spill(_, _) => false,
    }
  }
}

impl fmt::Display for RegisterSpill {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      RegisterSpill::Register(reg) => write!(f, "{reg}"),
      RegisterSpill::Spill(stack, _) => write!(f, "s{}", stack.0),
    }
  }
}

#[cfg(test)]
mod tests {
  use core::fmt;

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
    fn log(&mut self, msg: fmt::Arguments) {
      use std::fmt::Write;

      writeln!(self.out, "{msg}").unwrap();
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
    check_v(
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
        activating r0 at InstructionIndex(0)
        activating r1 at InstructionIndex(1)
        activating r2 at InstructionIndex(2)
        spilling r0 to assign r2 = Eax
        expiring r2 at InstructionIndex(3)
        activating r3 at InstructionIndex(3)
        spilling r1 to assign r3 = Edi
        expiring r0 at InstructionIndex(4)
        expiring r3 at InstructionIndex(4)
        activating r4 at InstructionIndex(4)
        expiring r4 at InstructionIndex(5)
        activating r5 at InstructionIndex(5)
        expiring r1 at InstructionIndex(6)
        expiring r5 at InstructionIndex(6)
        activating r6 at InstructionIndex(6)

        block 0:
          mov s0(0) = 0x01
          mov s1(1) = 0x00
          mov rax(7) = s0(0)
          mov rdi(8) = s1(1)
          syscall rax(2) = rax(7), rdi(8)
          mov rdi(3) = 0x02
          mov rax(9) = s0(0)
          syscall rax(4) = rax(9), rdi(3)
          mov rax(5) = 0x03
          mov rdi(10) = s1(1)
          syscall rax(6) = rax(5), rdi(10)
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
          mov rcx(2) = 0x03
          math(imul) rax(0) = rax(1), rcx(2)
          mov rdi(3) = rax(0)
          return r3
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
          call function 0 rdi(0), s1(1) =
          mov rsi(2) = 0x01
          call function 0 = rdi(0), rsi(2)
          mov rsi(3) = 0x02
          mov rdi(4) = s1(1)
          call function 0 = rdi(4), rsi(3)
          trap
      "#
      ],
    );
  }

  #[test]
  fn split_critical() {
    check(
      "
      block 0:
        call 0 r0 = 0x01
        call 1 = r0
      ",
      expect![@r#"
        block 0:
          mov rdi(1) = 0x01
          call function 0 rsi(0) = rdi(1)
          mov rdi(2) = rsi(0)
          call function 0 = rdi(2)
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
        activating r0 at InstructionIndex(0)
        activating r1 at InstructionIndex(1)
        spilling r0 to assign r1 = Edi

        block 0:
          mov s0(0) = 0x01
          mov rdi(1) = 0x02
          call function 0 = rdi(1)
          mov rdi(2) = s0(0)
          return r2
      "#
      ],
    );
  }

  #[test]
  fn save_clobbers() {
    check_v(
      "
      block 0:
        mov r0 = 0x01
        mov r1 = 0x02
        call extern = 0x02
        return r0, r1
      ",
      expect![@r#"
        activating r0 at InstructionIndex(0)
        activating r1 at InstructionIndex(1)
        activating r2 at InstructionIndex(2)
        spilling r0 to assign r2 = Edi

        block 0:
          mov s0(0) = 0x01
          mov rsi(1) = 0x02
          mov rdi(2) = 0x02
          call extern 0 = rdi(2)
          mov rdi(3) = s0(0)
          return r3, r1
      "#
      ],
    );
  }

  #[test]
  fn allocate_unused() {
    check_v(
      "
      block 0:
        mov r0 = 0x01
        mov r1 = 0x02
        trap
      ",
      expect![@r#"
        activating r0 at InstructionIndex(0)
        expiring r0 at InstructionIndex(1)
        activating r1 at InstructionIndex(1)

        block 0:
          mov rax(0) = 0x01
          mov rax(1) = 0x02
          trap
      "#
      ],
    );
  }

  #[test]
  fn assert_works() {
    check(
      "
      arg r0
      block 0:
        math(xor) r1 = r0, 0x01
        branch(eq) r2 = r1, 0x00
        mov r3 = 0x5555
        call 2 r4 = 0x01, r3, 0x11
        call 6 r5 =
        jump to block 1
      block 1:
        return
      ",
      expect![@r#"
        block 0:
          math(xor) rdi(1) = rdi(0), 0x01
          branch Equal to block 1 rax(2) = rdi(1), 0x00
          mov rsi(3) = 0x5555
          mov rdi(6) = 0x01
          mov rdx(7) = 0x11
          call function 0 rbx(4) = rdi(6), rsi(3), rdx(7)
          call function 0 rdi(5) =
          jump to block 1
        block 1:
          return
      "#],
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
