use std::fmt;

use rb_codegen::{
  Function, InstructionInput, InstructionOutput, Math, Opcode, Variable, VariableSize,
};
use smallvec::smallvec;

use crate::instruction::RegisterIndex;

pub struct VariableRegisters {
  registers: Vec<Register>,
}

struct Lifetimes {
  lifetimes: Vec<Option<Lifetime>>,
}

struct PinnedVariables {
  pinned: Vec<Option<RegisterIndex>>,

  changes: Vec<Change>,
}

enum Change {
  AddCopy { loc: InstructionLocation, from: Variable },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lifetime {
  def: InstructionLocation,

  first_use: InstructionLocation,
  last_use:  InstructionLocation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionLocation {
  pub block:       u32,
  pub instruction: u32,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Register {
  pub size:  RegisterSize,
  pub index: RegisterIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegisterSize {
  Bit8,
  Bit16,
  Bit32,
  Bit64,
}

pub enum CallingConvention {
  Syscall,
}

impl VariableRegisters {
  pub fn new() -> Self { VariableRegisters { registers: vec![] } }

  pub fn pass(&mut self, function: &mut Function) {
    let pinned = PinnedVariables::solve(function);
    let lifetimes = Lifetimes::solve(function);
    let mut used = [Option::<Variable>::None; 16];

    for (b, block) in function.blocks.iter().enumerate() {
      for (i, inst) in block.instructions.iter().enumerate() {
        let loc = InstructionLocation { block: b as u32, instruction: i as u32 };

        for output in &inst.output {
          if let InstructionOutput::Var(v) = *output {
            let size = match v.size() {
              VariableSize::Bit1 => continue,
              VariableSize::Bit8 => RegisterSize::Bit8,
              VariableSize::Bit16 => RegisterSize::Bit16,
              VariableSize::Bit32 => RegisterSize::Bit32,
              VariableSize::Bit64 => RegisterSize::Bit64,
            };

            if let Some(index) = pinned.get(v) {
              if used[index as usize].is_some_and(|u| lifetimes.is_used_at(u, loc)) {
                panic!("pinned register {index:?} is already in use");
              }
              self.set(v, Register { index, size });
              used[index as usize] = Some(v);
              continue;
            }

            'outer: for (index, used) in used.iter_mut().enumerate() {
              let index = unsafe { std::mem::transmute::<u8, RegisterIndex>(index as u8) };

              if used.is_none_or(|u| !lifetimes.is_used_at(u, loc)) {
                // If we overlap with a pinned variable, don't use that variable.
                for variable in lifetimes.overlaps_with(v) {
                  if let Some(i) = pinned.get(variable) {
                    if index == i {
                      continue 'outer;
                    }
                  }
                }

                *used = Some(v);
                self.set(v, Register { index, size });
                break;
              }
            }
          }
        }
      }
    }
  }

  pub fn set(&mut self, var: Variable, reg: Register) {
    if var.id() as usize >= self.registers.len() {
      self.registers.resize(var.id() as usize + 1, Register::RAX);
    }
    self.registers[var.id() as usize] = reg;
  }

  pub fn get(&self, var: Variable) -> Register { self.registers[var.id() as usize] }
}

impl Lifetimes {
  fn solve(function: &Function) -> Self {
    let mut l = Lifetimes { lifetimes: vec![] };

    for (b, block) in function.blocks.iter().enumerate() {
      for (i, inst) in block.instructions.iter().enumerate() {
        let loc = InstructionLocation { block: b as u32, instruction: i as u32 };

        for input in &inst.input {
          if let InstructionInput::Var(v) = input {
            l.add_use(*v, loc);
          }
        }

        for output in &inst.output {
          if let InstructionOutput::Var(v) = output {
            l.add_def(*v, loc);
          }
        }
      }
    }

    l
  }

  fn overlaps_with(&self, var: Variable) -> impl Iterator<Item = Variable> + '_ {
    let lifetime = self.lifetimes[var.id() as usize].unwrap();

    self.lifetimes.iter().enumerate().filter_map(move |(id, l)| {
      if let Some(l) = l {
        if !(l.last_use < lifetime.def || lifetime.last_use < l.def) {
          return Some(Variable::new(id as u32, var.size()));
        }
      }
      None
    })
  }

  fn is_used_at(&self, var: Variable, loc: InstructionLocation) -> bool {
    if let Some(l) = self.lifetimes[var.id() as usize] {
      l.first_use <= loc && loc < l.last_use
    } else {
      false
    }
  }

  fn add_use(&mut self, var: Variable, loc: InstructionLocation) {
    if self.lifetimes.len() <= var.id() as usize {
      self.lifetimes.resize(var.id() as usize + 1, None);
    }

    let prev = self.lifetimes[var.id() as usize];

    self.lifetimes[var.id() as usize] = Some(Lifetime {
      def:       prev.map_or(loc, |l| l.def),
      first_use: prev.map_or(loc, |l| l.first_use.min(loc)),
      last_use:  prev.map_or(loc, |l| l.last_use.max(loc)),
    });
  }

  fn add_def(&mut self, var: Variable, loc: InstructionLocation) {
    if self.lifetimes.len() <= var.id() as usize {
      self.lifetimes.resize(var.id() as usize + 1, None);
    }

    let prev = self.lifetimes[var.id() as usize];
    self.lifetimes[var.id() as usize] = Some(Lifetime {
      def:       loc,
      first_use: prev.map_or(loc, |l| l.first_use),
      last_use:  prev.map_or(loc, |l| l.last_use),
    });
  }
}

impl PinnedVariables {
  fn solve(function: &mut Function) -> Self {
    loop {
      let pinned = Self::solve_inner(function);

      if pinned.changes.is_empty() {
        return pinned;
      }

      for change in pinned.changes.iter().rev() {
        match *change {
          Change::AddCopy { loc, from } => {
            let to = Variable::new(
              function
                .blocks
                .iter()
                .flat_map(|b| {
                  b.instructions.iter().flat_map(|i| {
                    i.output.iter().filter_map(|o| {
                      if let InstructionOutput::Var(v) = o { Some(v.id()) } else { None }
                    })
                  })
                })
                .max()
                .unwrap(),
              from.size(),
            );

            function.blocks[loc.block as usize].instructions.insert(
              loc.instruction as usize,
              rb_codegen::Instruction {
                opcode: Opcode::Move,
                input:  smallvec![InstructionInput::Var(from)],
                output: smallvec![InstructionOutput::Var(to)],
              },
            );

            for instr in function.blocks[loc.block as usize].instructions
              [(loc.instruction + 1) as usize..]
              .iter_mut()
            {
              for input in instr.input.iter_mut() {
                if let InstructionInput::Var(v) = input
                  && *v == from
                {
                  *input = InstructionInput::Var(to);
                }
              }
            }

            for block in &mut function.blocks[loc.block as usize + 1..] {
              for instr in block.instructions.iter_mut() {
                for input in instr.input.iter_mut() {
                  if let InstructionInput::Var(v) = input
                    && *v == from
                  {
                    *input = InstructionInput::Var(to);
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  fn solve_inner(function: &Function) -> Self {
    let mut p = PinnedVariables { pinned: vec![], changes: vec![] };

    for (b, block) in function.blocks.iter().enumerate() {
      for (i, inst) in block.instructions.iter().enumerate() {
        let loc = InstructionLocation { block: b as u32, instruction: i as u32 };

        match inst.opcode {
          Opcode::Math(
            Math::Imul | Math::Umul | Math::Idiv | Math::Udiv | Math::Neg | Math::Not,
          ) => {
            let i0 = p.to_var(inst.input[0]);
            let o0 = p.to_var(inst.output[0]);
            p.pin(loc, i0, RegisterIndex::Eax);
            p.pin(loc, o0, RegisterIndex::Eax);
          }
          Opcode::Math(Math::Irem | Math::Urem) => {
            let i0 = p.to_var(inst.input[0]);
            let o0 = p.to_var(inst.output[0]);
            p.pin(loc, i0, RegisterIndex::Eax);
            p.pin(loc, o0, RegisterIndex::Edx);
          }
          Opcode::Math(Math::Ishr | Math::Ushr | Math::Shl) => {
            let i1 = p.to_var(inst.input[1]);
            p.pin(loc, i1, RegisterIndex::Ecx);
          }
          Opcode::Syscall => p.pin_cc(loc, CallingConvention::Syscall, &inst.input),
          _ => {}
        }
      }
    }

    p
  }

  fn get(&self, var: Variable) -> Option<RegisterIndex> {
    self.pinned.get(var.id() as usize).copied().flatten()
  }

  fn pin_cc(
    &mut self,
    loc: InstructionLocation,
    cc: CallingConvention,
    inputs: &[InstructionInput],
  ) {
    match cc {
      CallingConvention::Syscall => {
        let mut arg_index = 0;
        for input in inputs {
          if let InstructionInput::Var(v) = input {
            let reg = match arg_index {
              0 => Register::RAX,
              1 => Register::RDI,
              2 => Register::RSI,
              3 => Register::RDX,
              4 => Register::RCX,
              _ => panic!("too many syscall arguments"),
            };
            self.pin(loc, *v, reg.index);
            arg_index += 1;
          } else {
            panic!("expected variable input for syscall");
          }
        }
      }
    }
  }

  fn pin(&mut self, loc: InstructionLocation, var: Variable, index: RegisterIndex) {
    if self.pinned.len() <= var.id() as usize {
      self.pinned.resize(var.id() as usize + 1, None);
    }

    if let Some(pin) = self.pinned[var.id() as usize]
      && pin != index
    {
      self.changes.push(Change::AddCopy { loc, from: var });
    } else {
      self.pinned[var.id() as usize] = Some(index);
    }
  }

  fn to_var(&mut self, v: impl ToVar) -> Variable { v.to_var(self) }
}

trait ToVar {
  fn to_var(&self, p: &mut PinnedVariables) -> Variable;
}

impl ToVar for InstructionInput {
  fn to_var(&self, p: &mut PinnedVariables) -> Variable {
    match self {
      InstructionInput::Var(v) => *v,
      InstructionInput::Imm(_) => panic!("expected variable input, got immediate"),
    }
  }
}

impl ToVar for InstructionOutput {
  fn to_var(&self, p: &mut PinnedVariables) -> Variable {
    match self {
      InstructionOutput::Var(v) => *v,
      InstructionOutput::Syscall => panic!("cannot turn syscall into var"),
    }
  }
}

macro_rules! registers {
  (
    $(
      $const:ident: $str:expr, $size:ident, $index:ident;
    )*
  ) => {
    #[allow(unused)]
    impl Register {
      $(
        pub const $const: Register = Register { size: RegisterSize::$size, index: RegisterIndex::$index };
      )*
    }

    impl fmt::Debug for Register {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.size, self.index) {
          $(
            (RegisterSize::$size, RegisterIndex::$index) => write!(f, $str),
          )*
        }
      }
    }
  };
}

registers! {
  AL: "al", Bit8, Eax;
  CL: "cl", Bit8, Ecx;
  DL: "dl", Bit8, Edx;
  BL: "bl", Bit8, Ebx;
  SPL: "spl", Bit8, Esp;
  BPL: "bpl", Bit8, Ebp;
  SIL: "sil", Bit8, Esi;
  DIL: "dil", Bit8, Edi;

  AX: "ax", Bit16, Eax;
  CX: "cx", Bit16, Ecx;
  DX: "dx", Bit16, Edx;
  BX: "bx", Bit16, Ebx;
  SP: "sp", Bit16, Esp;
  BP: "bp", Bit16, Ebp;
  SI: "si", Bit16, Esi;
  DI: "di", Bit16, Edi;

  EAX: "eax", Bit32, Eax;
  ECX: "ecx", Bit32, Ecx;
  EDX: "edx", Bit32, Edx;
  EBX: "ebx", Bit32, Ebx;
  ESP: "esp", Bit32, Esp;
  EBP: "ebp", Bit32, Ebp;
  ESI: "esi", Bit32, Esi;
  EDI: "edi", Bit32, Edi;

  RAX: "rax", Bit64, Eax;
  RCX: "rcx", Bit64, Ecx;
  RDX: "rdx", Bit64, Edx;
  RBX: "rbx", Bit64, Ebx;
  RSP: "rsp", Bit64, Esp;
  RBP: "rbp", Bit64, Ebp;
  RSI: "rsi", Bit64, Esi;
  RDI: "rdi", Bit64, Edi;
}
