pub struct Instruction {
  pub rex:       Option<Rex>,
  pub opcode:    Opcode,
  pub mod_rm:    Option<ModRm>,
  pub immediate: Immediate,
}

#[derive(Clone, Copy)]
pub enum Rex {
  W,
}

const _INSTR_SIZE: () = assert!(std::mem::size_of::<Instruction>() == 16);
const _REX_SIZE: () = assert!(std::mem::size_of::<Option<Rex>>() == 1);

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Register {
  Eax,
  Ecx,
  Edx,
  Ebx,
  Esp,
  Ebp,
  Esi,
  Edi,
}

#[derive(Clone, Copy)]
pub struct Opcode {
  code: [u8; 3],
  len:  u8,
}

#[derive(Clone, Copy)]
pub struct ModRm(u8);

#[derive(Clone, Copy)]
#[repr(packed)]
pub struct Immediate {
  len:   u8,
  value: u64,
}

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

  pub fn mod_bits(&self) -> u8 { (self.0 >> 6) & 0b11 }
  pub fn reg_bits(&self) -> u8 { (self.0 >> 3) & 0b111 }
  pub fn rm_bits(&self) -> u8 { self.0 & 0b111 }
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

impl Immediate {
  pub const fn empty() -> Self { Immediate { len: 0, value: 0 } }
  pub const fn i8(value: u8) -> Self { Immediate { len: 1, value: value as u64 } }
  pub const fn i16(value: u16) -> Self { Immediate { len: 2, value: value as u64 } }
  pub const fn i32(value: u32) -> Self { Immediate { len: 4, value: value as u64 } }
  pub const fn i64(value: u64) -> Self { Immediate { len: 8, value: value as u64 } }

  pub const fn is_empty(&self) -> bool { self.len == 0 }
  pub const fn len(&self) -> u8 { self.len }
  pub const fn value(&self) -> u64 { self.value }
}

impl Instruction {
  pub fn new(opcode: Opcode) -> Self {
    Instruction { rex: None, opcode, mod_rm: None, immediate: Immediate::empty() }
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

    if !self.immediate.is_empty() {
      let imm_bytes = self.immediate.value().to_le_bytes();
      let imm_len = self.immediate.len() as usize;
      buf[len..len + imm_len].copy_from_slice(&imm_bytes[..imm_len]);
      len += imm_len;
    }

    (buf, len)
  }

  pub fn with_rex(mut self, rex: Rex) -> Self {
    self.rex = Some(rex);
    self
  }

  pub fn with_reg(self, dst: Register, src: Register) -> Self {
    self.with_mod_rm(ModRm::from_parts(0b11, dst as u8, src as u8))
  }

  pub fn with_disp(self, reg: Register, disp: i32) -> Self {
    self
      .with_mod_rm(ModRm::from_parts(0b00, reg as u8, 0b101))
      .with_immediate(Immediate::i32(disp as u32))
  }

  pub fn with_mod_rm(mut self, mod_rm: ModRm) -> Self {
    self.mod_rm = Some(mod_rm);
    self
  }

  // NB: This will always be encoded in the minimum number of bytes needed to
  // store the given immediate.
  pub fn with_immediate(mut self, immediate: Immediate) -> Self {
    self.immediate = immediate;
    self
  }

  pub fn immediate(&self) -> Immediate { self.immediate }
}

impl Opcode {
  pub const MOV_RM_IMM_8: Opcode = Opcode::new([0xc6]);
  pub const MOV_RM_IMM_16: Opcode = Opcode::new([0xc7]);
  pub const LEA: Opcode = Opcode::new([0x8d]);
  pub const SYSCALL: Opcode = Opcode::new([0x0f, 0x05]);
}
