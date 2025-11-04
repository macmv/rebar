use std::collections::{BTreeMap, HashMap, HashSet, hash_map::Entry};

use rb_codegen::{
  BlockId, Immediate, Instruction, InstructionInput, InstructionOutput, Math, Opcode, Variable,
};
use smallvec::SmallVec;

use super::*;

#[derive(Default)]
pub struct ValueUses {
  pub variables: HashMap<Variable, VariableInfo>,

  pub variables_to_block: HashMap<Variable, BlockId>,

  current_block: BlockId,
}

#[derive(Debug)]
pub struct VariableInfo {
  pub value:    VariableValue,
  pub used_by:  HashSet<Variable>,
  pub required: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VariableValue {
  Unknown,
  Immediate(Immediate),
  Variable(Variable),
  Compare { inputs: Box<(VariableValue, VariableValue)> },
  Math { math: Math, input: Vec<VariableValue> },

  Phi { from: BTreeMap<BlockId, VariableValue> },
  DefinedLater,
}

impl ValueUses {
  pub const ID: AnalysisPassId = AnalysisPassId("value_uses");
}

impl AnalysisPass for ValueUses {
  fn id() -> AnalysisPassId { Self::ID }

  fn pass(&mut self, _: &mut Analysis, function: &Function) {
    for arg in function.args() {
      self.set(arg, VariableValue::Unknown);
    }

    for block in function.blocks() {
      self.current_block = block;

      for phi in &function.block(block).phis {
        for &from in phi.from.values().flatten() {
          if !self.variables.contains_key(&from) {
            self.set(from, VariableValue::DefinedLater);
          }

          self.variables.get_mut(&from).unwrap().used_by.insert(phi.to);
        }

        let values = phi
          .from
          .iter()
          .filter_map(|(&block, &var)| var.map(|v| (block, v)))
          .map(|(block, var)| {
            (
              block,
              self.simplify_value(
                &mut HashSet::new(),
                &mut HashSet::new(),
                VariableValue::Variable(var),
              ),
            )
          })
          .collect();

        self.set(phi.to, VariableValue::Phi { from: values });
      }

      for instr in &function.block(block).instructions {
        self.pass_instr(instr);
      }

      if let rb_codegen::TerminatorInstruction::Return(ref rets) = function.block(block).terminator
      {
        for ret in rets {
          if let InstructionInput::Var(var) = ret {
            self.mark_required(*var);
          }
        }
      }
    }

    // TODO: Debug output?
    /*
    for (kind, ids) in &self.variables_by_kind {
      println!("the variable kind {kind:?} has the following ids:");
      for (id, value) in ids {
        println!("  - id {id:?} with value {value:?}");
      }
    }

    println!("the following variables were seen:");
    for (id, var) in &self.variables {
      println!("  - id {id:?} with value {var:?}");
    }
    */
  }
}

impl ValueUses {
  fn pass_instr(&mut self, instr: &Instruction) {
    if matches!(instr.opcode, Opcode::Syscall | Opcode::Call(_)) {
      for input in &instr.input {
        if let InstructionInput::Var(var) = input {
          self.mark_required(*var);
        }
      }
    }

    let out = match *instr.output.as_slice() {
      [] => return,
      [InstructionOutput::Var(v)] => v,
      _ => todo!("handle non-variable outputs in ValueUses analysis"),
    };

    for input in &instr.input {
      if let InstructionInput::Var(var) = input {
        self.attach_use(out, *var);
      }
    }

    match instr.opcode {
      Opcode::Move => {
        let v = self.input_to_value(instr.input[0]);
        self.set(out, v);
      }
      Opcode::Lea(_) => {}
      Opcode::Call(_) => {
        self.set(out, VariableValue::Unknown);
        self.mark_required(out);
      }
      Opcode::Syscall => {}
      Opcode::Compare(_) => {
        let cmp = VariableValue::Compare {
          inputs: Box::new((
            self.input_to_value(instr.input[0]),
            self.input_to_value(instr.input[1]),
          )),
        };

        self.set(out, cmp);
      }
      Opcode::Math(math) => {
        self.set(
          out,
          VariableValue::Math {
            math,
            input: instr.input.iter().map(|i| self.actual_value(*i)).collect(),
          },
        );
      }

      Opcode::Branch(_, _) => {
        self.set(out, VariableValue::Unknown);
        self.mark_required(out);
      }

      Opcode::StackAddr(_) | Opcode::StackLoad(_, _) | Opcode::StackStore(_, _) => {
        self.set(out, VariableValue::Unknown);
      }
    }

    for output in &instr.output {
      let InstructionOutput::Var(var) = output;
      if !self.variables.contains_key(var) {
        self.set(*var, VariableValue::Unknown);
      }
    }
  }

  pub fn variable(&self, var: Variable) -> &VariableInfo {
    self.variable_opt(var).unwrap_or_else(|| panic!("no such variable with the id {var:?}"))
  }
  pub fn variable_opt(&self, var: Variable) -> Option<&VariableInfo> { self.variables.get(&var) }

  #[track_caller]
  fn attach_use(&mut self, out: Variable, input: Variable) {
    self.variables.get_mut(&input).expect("no such variable").used_by.insert(out);
  }
  #[track_caller]
  fn mark_required(&mut self, var: Variable) {
    self.variables.get_mut(&var).expect("no such variable").required = true;
  }

  pub fn actual_value(&self, input: InstructionInput) -> VariableValue {
    let v = self.input_to_value(input);
    self.simplify_value(&mut HashSet::new(), &mut HashSet::new(), v)
  }

  fn simplify_value(
    &self,
    phis: &mut HashSet<BlockId>,
    seen: &mut HashSet<Variable>,
    value: VariableValue,
  ) -> VariableValue {
    match value {
      VariableValue::Variable(var) => {
        if seen.insert(var) {
          match self.variable(var).value {
            VariableValue::DefinedLater => value,
            ref v => {
              let is_phi = matches!(v, VariableValue::Phi { .. });
              let block = self.variables_to_block[&var];

              if is_phi && phis.contains(&block) {
                return value;
              }

              if is_phi {
                phis.insert(block);
              }
              let simplified = self.simplify_value(phis, seen, v.clone());
              if is_phi {
                phis.remove(&block);
              }
              simplified
            }
          }
        } else {
          value
        }
      }
      VariableValue::Immediate(_) => value,
      VariableValue::Compare { inputs } => {
        let a = self.simplify_value(phis, seen, inputs.0);
        let b = self.simplify_value(phis, seen, inputs.1);

        VariableValue::Compare { inputs: Box::new((a, b)) }
      }

      VariableValue::Phi { from } => {
        let mut new_from = BTreeMap::new();
        for (block, v) in from {
          new_from.insert(block, self.simplify_value(phis, &mut HashSet::new(), v));
        }

        // TODO: Merge phis when multiple values are the same, but not all?
        let first = new_from.values().next().unwrap();
        if new_from.values().all(|v| v == first) {
          first.clone()
        } else {
          VariableValue::Phi { from: new_from }
        }
      }

      VariableValue::Math { math, input } => {
        let simplified: SmallVec<[VariableValue; 2]> =
          input.into_iter().map(|v| self.simplify_value(phis, seen, v)).collect();

        if let Some(c) = const_eval(math, &simplified) {
          VariableValue::Immediate(c)
        } else {
          VariableValue::Math { math, input: simplified.into_vec() }
        }
      }

      _ => value,
    }
  }

  #[track_caller]
  fn input_to_value(&self, input: InstructionInput) -> VariableValue {
    match input {
      InstructionInput::Var(var) => VariableValue::Variable(var),
      InstructionInput::Imm(imm) => VariableValue::Immediate(imm),
    }
  }

  #[track_caller]
  fn set(&mut self, v: Variable, value: VariableValue) {
    match self.variables.entry(v) {
      Entry::Occupied(mut o) => {
        if o.get().value != VariableValue::DefinedLater {
          panic!("cannot reassign variable");
        }
        o.get_mut().value = value.clone();
      }
      Entry::Vacant(v) => {
        v.insert(VariableInfo {
          value:    value.clone(),
          used_by:  HashSet::new(),
          required: false,
        });
      }
    }
    self.variables_to_block.insert(v, self.current_block);
  }
}

fn const_eval(m: Math, args: &[VariableValue]) -> Option<Immediate> {
  macro_rules! bin_op {
    ($op:ident, $func:ident) => {
      if m == Math::$op
        && let (VariableValue::Immediate(a), VariableValue::Immediate(b)) = (&args[0], &args[1])
      {
        match (a, b) {
          (Immediate::Signed(a), Immediate::Signed(b)) => {
            return Some(Immediate::Signed(a.$func(*b)));
          }
          (Immediate::Unsigned(a), Immediate::Unsigned(b)) => {
            return Some(Immediate::Unsigned(a.$func(*b)));
          }
          _ => {}
        }
      }
    };
  }

  bin_op!(Add, wrapping_add);

  None
}

#[cfg(test)]
mod tests {
  use crate::{tests::parse, v};

  use super::*;

  #[test]
  fn deps_works() {
    let mut ast = parse(
      r#"
      block 0:
        mov r0 = 0x00
        mov r1 = r0
        jump to block 1
      block 1:
        r2 = phi(block 0 -> r1, block 1 -> r6)
        r3 = phi(block 0 -> r0, block 1 -> r5)
        mov r4 = r2
        math(add) r5 = r4, 0x02
        mov r6 = r5
        jump to block 1
      "#,
    );

    let vu = ast.pass::<ValueUses>();

    // There is a loop of variables.
    assert!(&vu.variables[&v!(6)].used_by.contains(&v!(2)));
    assert!(&vu.variables[&v!(2)].used_by.contains(&v!(4)));
    assert!(&vu.variables[&v!(4)].used_by.contains(&v!(5)));
    assert!(&vu.variables[&v!(5)].used_by.contains(&v!(6)));

    // ast.full_optimize();

    ast.check(expect![@r#"
      block 0:
        mov r0 = 0x00
        mov r1 = r0
        jump to block 1
      block 1:
        r2 = phi(block 0 -> r1, block 1 -> r6)
        r3 = phi(block 0 -> r0, block 1 -> r5)
        mov r4 = r2
        math(add) r5 = r4, 0x02
        mov r6 = r5
        jump to block 1
    "#]);
  }

  /*
  #[test]
  fn actual_value_produces_phis() {
    let mut ast = parse(
      r#"
      block 0:
        mov A(v0) 0x00
        mov [0x80](v1) A(v0)
        jump to block 1
      block 1:
        [0x80](v2) = phi(block 0 -> v1, block 1 -> v6)
        A(v3) = phi(block 0 -> v0, block 1 -> v5)
        mov A(v4) [0x80](v2)
        math A(v5) = A(v4) Add 0x02
        mov [0x80](v6) A(v5)
        jump to block 1
    "#,
    );

    let vu = ast.pass::<crate::analysis::value_uses::ValueUses>();
    assert_eq!(
      vu.actual_value(Value::Variable(v!(2))),
      VariableValue::Phi {
        from: BTreeMap::from([
          (BlockId::new(0), VariableValue::Direct(Value::Const(0))),
          (
            BlockId::new(1),
            VariableValue::Binary {
              inputs: Box::new((
                VariableValue::Direct(Value::Variable(v!(2))),
                VariableValue::Direct(Value::Const(2))
              )),
              op:     BinaryOp::Add,
            }
          ),
        ]),
      }
    );
    assert_eq!(vu.actual_value(Value::Variable(v!(2))), vu.actual_value(Value::Variable(v!(4))));
    assert_eq!(vu.actual_value(Value::Variable(v!(2))), vu.actual_value(Value::Variable(v!(3))));
  }

  #[test]
  fn volatile_read_turns_into_variable() {
    let mut ast = parse(
      r#"
      block 0:
        mov A(v0) [0x00ff]
        mov A(v1) [0x00ff]
        mov [0x80](v2) A(v1)
        mov A(v3) [0x80](v2)
        jump to block 1
      block 1:
        jump to block 1
    "#,
    );

    let vu = ast.pass::<crate::analysis::value_uses::ValueUses>();
    assert_eq!(
      vu.actual_value(Value::Variable(v!(0))),
      VariableValue::Direct(Value::Variable(v!(0)))
    );
    assert_eq!(
      vu.actual_value(Value::Variable(v!(1))),
      VariableValue::Direct(Value::Variable(v!(1)))
    );
    assert_eq!(
      vu.actual_value(Value::Variable(v!(2))),
      VariableValue::Direct(Value::Variable(v!(1)))
    );
    assert_eq!(vu.previous_value(v!(2)).unwrap().1, VariableValue::Direct(Value::Variable(v!(1))));
  }
  */
}
