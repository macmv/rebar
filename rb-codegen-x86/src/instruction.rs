pub struct Instruction {
  pub rex:    Option<Rex>,
  pub opcode: Opcode,
  pub mod_rm: Option<ModRm>,

  // This is an `Option<u64>` but it only uses 9 bytes instead of 16.
  immediate_set: bool,
  immediate:     u64,
}

#[derive(Clone, Copy)]
pub enum Rex {
  W,
}

const _INSTR_SIZE: () = assert!(std::mem::size_of::<Instruction>() == 16);
const _REX_SIZE: () = assert!(std::mem::size_of::<Option<Rex>>() == 1);

#[derive(Clone, Copy)]
pub struct Opcode {
  code: [u8; 3],
  len:  u8,
}

#[derive(Clone, Copy)]
pub struct ModRm(u8);

impl From<u8> for Opcode {
  fn from(byte: u8) -> Self { Opcode::new([byte]) }
}
impl From<[u8; 2]> for Opcode {
  fn from(bytes: [u8; 2]) -> Self { Opcode::new(bytes) }
}
impl From<[u8; 3]> for Opcode {
  fn from(bytes: [u8; 3]) -> Self { Opcode::new(bytes) }
}

impl ModRm {
  pub fn from_parts(mod_bits: u8, reg_bits: u8, rm_bits: u8) -> Self {
    debug_assert!(mod_bits < 4);
    debug_assert!(reg_bits < 8);
    debug_assert!(rm_bits < 8);

    ModRm((mod_bits << 6) | (reg_bits << 3) | rm_bits)
  }

  fn mod_bits(&self) -> u8 { (self.0 >> 6) & 0b11 }
  fn reg_bits(&self) -> u8 { (self.0 >> 3) & 0b111 }
  fn rm_bits(&self) -> u8 { self.0 & 0b111 }
}

impl Opcode {
  pub const fn new<const N: usize>(bytes: [u8; N]) -> Self {
    assert!(N >= 1 && N <= 3);
    let mut code = [0; 3];
    unsafe {
      *code.as_mut_ptr() = bytes[0];
      if N >= 2 {
        *code.as_mut_ptr().add(1) = bytes[1];
      }
      if N >= 3 {
        *code.as_mut_ptr().add(2) = bytes[2];
      }
    }
    Opcode { code, len: N as u8 }
  }

  pub fn bytes(&self) -> &[u8] { &self.code[..self.len as usize] }
}

impl Instruction {
  pub fn new(opcode: Opcode) -> Self {
    Instruction { rex: None, opcode, mod_rm: None, immediate_set: false, immediate: 0 }
  }

  pub fn encode(&self) -> ([u8; 15], usize) {
    let mut buf = [0; 15];
    let mut len = 0;
    if let Some(rex) = self.rex {
      buf[len] = match rex {
        Rex::W => 0x48,
      };
      len += 1;
    }

    buf[len..len + self.opcode.len as usize]
      .copy_from_slice(&self.opcode.code[..self.opcode.len as usize]);
    len += self.opcode.len as usize;

    if let Some(ModRm(mod_rm)) = self.mod_rm {
      buf[len] = mod_rm;
      len += 1;
    }

    if let Some(imm) = self.immediate() {
      let imm_bytes = imm.to_le_bytes();
      let imm_len = if imm <= u8::MAX as u64 {
        1
      } else if imm <= u16::MAX as u64 {
        2
      } else if imm <= u32::MAX as u64 {
        4
      } else {
        8
      };
      buf[len..len + imm_len].copy_from_slice(&imm_bytes[..imm_len]);
      len += imm_len;
    }

    (buf, len)
  }

  pub fn with_rex(mut self, rex: Rex) -> Self {
    self.rex = Some(rex);
    self
  }

  pub fn with_mod_rm(mut self, mod_rm: ModRm) -> Self {
    self.mod_rm = Some(mod_rm);
    self
  }

  // NB: This will always be encoded in the minimum number of bytes needed to
  // store the given immediate.
  pub fn with_immediate(mut self, immediate: u64) -> Self {
    self.immediate_set = true;
    self.immediate = immediate;
    self
  }

  pub fn immediate(&self) -> Option<u64> {
    if self.immediate_set { Some(self.immediate) } else { None }
  }
}

impl Opcode {
  pub const MOV_RAX_IMM: Opcode = Opcode::new([0xb8]);
  pub const MOV_RDI_IMM: Opcode = Opcode::new([0xbf]);
  pub const SYSCALL: Opcode = Opcode::new([0x0f, 0x05]);
}
