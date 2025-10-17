use std::collections::BTreeMap;

use rb_codegen::{
  Block, BlockId, Function, Instruction, Math, Opcode, Phi, Signature, Variable, VariableSize,
};

#[macro_export]
macro_rules! v {
  ($x:expr) => {
    v!($x, Bit64)
  };
  ($x:expr, $size:ident) => {
    Variable::new($x, rb_codegen::VariableSize::$size)
  };
}

pub fn parse(asm: &str) -> Function {
  let mut function =
    Function { sig: Signature { args: vec![], rets: vec![] }, blocks: Vec::new() };

  for line in asm.lines() {
    let line = line.trim();
    if line.is_empty() {
      continue;
    }

    if let Some(id) = line.strip_prefix("block ") {
      let id = id.strip_suffix(':').unwrap();
      let id = id.parse::<u32>().unwrap();
      if id != function.blocks.len() as u32 {
        panic!("out of order blocks");
      }

      function.blocks.push(Block::default());
      continue;
    }

    let (first_word, args) = line.split_once(' ').unwrap();
    let opcode = match first_word {
      "mov" => Opcode::Move,
      "math(abs)" => Opcode::Move,
      "math(add)" => Opcode::Math(Math::Add),
      "math(sub)" => Opcode::Math(Math::Sub),
      "math(imul)" => Opcode::Math(Math::Imul),
      "math(umul)" => Opcode::Math(Math::Umul),
      "math(idiv)" => Opcode::Math(Math::Idiv),
      "math(udiv)" => Opcode::Math(Math::Udiv),
      "math(irem)" => Opcode::Math(Math::Irem),
      "math(urem)" => Opcode::Math(Math::Urem),
      "math(and)" => Opcode::Math(Math::And),
      "math(or)" => Opcode::Math(Math::Or),
      "math(xor)" => Opcode::Math(Math::Xor),
      "math(shl)" => Opcode::Math(Math::Shl),
      "math(ushr)" => Opcode::Math(Math::Ushr),
      "math(ishr)" => Opcode::Math(Math::Ishr),
      "math(not)" => Opcode::Math(Math::Not),
      "math(neg)" => Opcode::Math(Math::Neg),

      "jump" => {
        let args = args.strip_prefix("to block ").unwrap();
        let target = args.parse::<u32>().unwrap();

        function.blocks.last_mut().unwrap().terminator =
          rb_codegen::TerminatorInstruction::Jump(BlockId::new(target));
        continue;
      }

      _ if line.contains("phi") => {
        function.blocks.last_mut().unwrap().phis.push(parse_phi(line));
        continue;
      }

      _ => panic!("unknown instruction: {line}"),
    };

    function.blocks.last_mut().unwrap().instructions.push(Instruction {
      opcode,
      input: smallvec![],
      output: smallvec![],
    });
  }

  function
}

fn parse_phi(s: &str) -> Phi {
  let (to, rest) = s.split_once(" = ").unwrap();

  let s = rest.strip_prefix("phi(").unwrap().strip_suffix(")").unwrap();

  let ids = s
    .split(',')
    .map(|s| {
      let (lhs, rhs) = s.split_once(" -> ").unwrap();
      let block = lhs.trim().strip_prefix("block ").unwrap();
      let block = if block == "before" {
        BlockId::new(0) // TODO
      } else {
        BlockId::new(block.parse::<u32>().unwrap())
      };

      (block, parse_variable_id(rhs))
    })
    .collect();

  Phi { to: parse_variable_id(to.trim()), from: ids }
}

fn parse_hex(s: &str) -> Option<u16> {
  let s = s.strip_prefix("0x")?;
  Some(u16::from_str_radix(s, 16).ok()?)
}

fn parse_variable_id(s: &str) -> Variable {
  let size = match s.chars().next() {
    Some('r') => VariableSize::Bit64,
    Some('e') => VariableSize::Bit32,
    Some('x') => VariableSize::Bit16,
    Some('l') => VariableSize::Bit8,
    Some('b') => VariableSize::Bit1,
    _ => panic!("unknown variable: {s}"),
  };

  let id = s[1..].parse::<u32>().unwrap();
  Variable::new(id, size)
}
