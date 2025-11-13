use std::{
  collections::{BTreeMap, HashMap, HashSet},
  fmt,
  ops::Range,
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
  saved:     RegisterMap<bool>,
}

trait RegallocDebug {
  fn log(&mut self, msg: fmt::Arguments) { let _ = msg; }
}

struct Regalloc<'a> {
  dom:      &'a DominatorTree,
  function: &'a mut Function,

  state: RegallocState<'a>,
}

struct NopDebug;

impl RegallocDebug for NopDebug {}

struct RegallocState<'a> {
  vu:    &'a ValueUses,
  alloc: &'a mut VariableRegisters,
  #[cfg(debug_assertions)]
  debug: &'a mut dyn RegallocDebug,
  #[cfg(not(debug_assertions))]
  debug: &'a mut NopDebug,

  intervals: HashMap<Variable, Interval>,
}

#[derive(Debug, Default)]
struct Interval {
  segments: Vec<Range<InstructionIndex>>,
  assigned: Option<RegisterIndex>,
}

#[derive(Clone, Copy)]
struct RegisterMap<T> {
  values: [Option<T>; RegisterIndex::COUNT],
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct InstructionIndex(usize);

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

    let intervals = live_intervals(function);
    let mut intervals = intervals.into_iter().collect::<Vec<(Variable, Interval)>>();
    intervals.sort_unstable_by_key(|(_, interval)| interval.segments.first().unwrap().start);

    let mut regs = VariableRegisters::default();

    let mut active = HashSet::new();
    for i in 0..intervals.len() {
      let &(var, ref interval) = &intervals[i];

      active.retain(|active_var| {
        let active_interval = &intervals.iter().find(|(v, _)| v == active_var).unwrap().1;

        let active_end = active_interval.segments.last().unwrap().end;
        let current_start = interval.segments.first().unwrap().start;

        if active_end <= current_start {
          debug.log(format_args!("expiring {active_var} at {current_start:?}",));
          false
        } else {
          true
        }
      });

      debug.log(format_args!("activating {var} at {:?}", interval.segments.first().unwrap().start));
      active.insert(var);

      for reg_index in RegisterIndex::all() {
        if active.iter().all(|active_var| {
          let active_interval = &intervals.iter().find(|(v, _)| v == active_var).unwrap().1;
          active_interval.assigned != Some(*reg_index)
        }) {
          intervals[i].1.assigned = Some(*reg_index);
          regs.registers.set_with(
            var,
            Register { index: *reg_index, size: var_to_reg_size(var.size()).unwrap() },
            || Register::RAX,
          );
          break;
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

fn imm_to_reg(function: &mut Function) {
  let last_var = function
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
    .unwrap_or(Variable::new(0, VariableSize::Bit64));
  let mut next_var_id = last_var.id() + 1;

  for block in function.blocks() {
    let mut i = 0;
    while i < function.block(block).instructions.len() {
      let block = function.block_mut(block);

      for j in 0..block.instructions[i].input.len() {
        let instr = &mut block.instructions[i];
        let req = Requirement::for_input(&instr, j);
        let input = &mut instr.input[j];

        match (*input, req) {
          (_, Requirement::None) => continue,
          (InstructionInput::Var(_), _) => continue,
          (InstructionInput::Imm(_), _) => {
            let prev_input = input.clone();
            let tmp = Variable::new(next_var_id, VariableSize::Bit64);
            next_var_id += 1;
            *input = InstructionInput::Var(tmp);

            block.instructions.insert(
              i,
              Instruction {
                opcode: Opcode::Move,
                input:  smallvec![prev_input],
                output: smallvec![tmp.into()],
              },
            );
            i += 1;
          }
        }
      }

      i += 1;
    }
  }
}

fn live_intervals(function: &Function) -> HashMap<Variable, Interval> {
  let mut intervals = HashMap::<Variable, Interval>::new();

  // TODO: Value-uses and dominator tree, but this'll work for now.
  let mut i = 0;
  for block in function.blocks() {
    let block = function.block(block);
    for instr in block.instructions.iter() {
      let index = InstructionIndex(i);

      for input in &instr.input {
        if let InstructionInput::Var(v) = input {
          let interval = intervals.entry(*v).or_default();

          if interval.segments.is_empty() {
            interval.segments.push(Range { start: index, end: InstructionIndex(0) });
          }

          interval.segments.last_mut().unwrap().end = InstructionIndex(i + 1);
        }
      }

      for output in &instr.output {
        let InstructionOutput::Var(v) = output;
        let interval = intervals.entry(*v).or_default();

        if interval.segments.is_empty() {
          interval.segments.push(Range { start: index, end: InstructionIndex(0) });
        }

        interval.segments.last_mut().unwrap().end = InstructionIndex(i + 1);
      }

      i += 1;
    }

    match &block.terminator {
      TerminatorInstruction::Return(rets) => {
        for arg in rets {
          if let InstructionInput::Var(v) = arg {
            let interval = intervals.entry(*v).or_default();

            if interval.segments.is_empty() {
              interval
                .segments
                .push(Range { start: InstructionIndex(i), end: InstructionIndex(0) });
            }

            interval.segments.last_mut().unwrap().end = InstructionIndex(i + 1);
          }
        }
      }
      _ => {}
    }
    i += 1;
  }

  intervals
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

  fn for_output(regalloc: &Regalloc, instr: &Instruction, index: usize) -> Option<RegisterIndex> {
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

impl<T> Default for RegisterMap<T> {
  fn default() -> Self { Self::new() }
}

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
          mov rax(3) = rdi(0)
          mov rdi(2) = rsi(1)
          mov rbx(8) = rdi(2)
          mov rdi(4) = rax(3)
          mov rsi(5) = 0x01
          call function 0 = rdi(4), rsi(5)
          mov rbx(6) = rax(3)
          mov rsi(7) = 0x02
          call function 0 = rdi(2), rsi(7)
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
        = mov r0 = 0x01
        marking r0(Edi) active
        = call function 0 = 0x02
        extern clobbers register Edi, rehoming r0
        rehoming r0(Edi) -> r1(Ebx)
        marking r1(Ebx) active
        + mov r1 = r0
        + mov r2 = Unsigned(2)
        marking r2(Edi) active
        freeing r2(Edi)
        + mov r3 = r1

        block 0:
          mov rdi(0) = 0x01
          mov rbx(1) = rdi(0)
          mov rdi(2) = 0x02
          call function 0 = rdi(2)
          mov rdi(3) = rbx(1)
          return r3
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
        preference: r0 -> Edi at <block 0, instr 3>
        preference: r1 -> Esi at <block 0, instr 3>
        = mov r0 = 0x01
        marking r0(Edi) active
        = mov r1 = 0x02
        marking r1(Esi) active
        = call extern 0 = 0x02
        extern clobbers register Esi, rehoming r1
        rehoming r1(Esi) -> r2(Ebx)
        marking r2(Ebx) active
        + mov r2 = r1
        extern clobbers register Edi, rehoming r0
        rehoming r0(Edi) -> r3(Ebp)
        marking r3(Ebp) active
        + mov r3 = r0
        + mov r4 = Unsigned(2)
        marking r4(Edi) active
        freeing r4(Edi)
        + mov r5 = r3
        + mov r6 = r2

        block 0:
          mov rdi(0) = 0x01
          mov rsi(1) = 0x02
          mov rbx(2) = rsi(1)
          mov rbp(3) = rdi(0)
          mov rdi(4) = 0x02
          call extern 0 = rdi(4)
          mov rdi(5) = rbp(3)
          mov rsi(6) = rbx(2)
          return r5, r6
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
