use rb_codegen::Variable;

use crate::instruction::Register;

pub struct VariableRegisters {
  registers: Vec<Register>,
}

impl VariableRegisters {
  pub fn new(num_vars: u32) -> Self {
    VariableRegisters { registers: vec![Register::Rax; num_vars as usize] }
  }

  pub fn set(&mut self, var: Variable, reg: Register) {
    self.registers[var.as_u32() as usize] = reg;
  }

  pub fn get(&self, var: Variable) -> Register { self.registers[var.as_u32() as usize] }
}
