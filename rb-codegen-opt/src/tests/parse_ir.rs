use std::collections::BTreeMap;

use rb_codegen::{
  Block, BlockId, Function, Instruction, Opcode, Signature, Variable, VariableSize,
};

#[macro_export]
macro_rules! v {
  ($x:expr) => {
    v!($x, A)
  };
  ($x:expr, A) => {
    Variable { kind: VariableKind::Register(Register::A), id: VariableId::new($x) }
  };
  ($x:expr, Memory($addr:expr)) => {
    Variable { kind: VariableKind::Memory { addr: $addr }, id: VariableId::new($x) }
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

      function.blocks.push(Block {
        instructions: vec![],
        terminator:   rb_codegen::TerminatorInstruction::Trap,
      });
      continue;
    }

    let (first_word, args) = line.split_once(' ').unwrap();
    match first_word {
      "mov" => {
        function.blocks.last_mut().unwrap().instructions.push(Instruction {
          opcode: Opcode::Move,
          output: smallvec![],
          input:  smallvec![],
        });
      }

      "jump" => {
        let args = args.strip_prefix("to block ").unwrap();
        let target = args.parse::<u32>().unwrap();

        function.blocks.last_mut().unwrap().terminator =
          rb_codegen::TerminatorInstruction::Jump(BlockId::new(target));
      }

      _ => panic!("unknown instruction: {line}"),
    }
  }

  function
}

// TODO

fn parse_phi(s: &str) -> BTreeMap<BlockId, Variable> {
  let s = s.strip_prefix("phi(").unwrap().strip_suffix(")").unwrap();

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

  ids
}

fn parse_hex(s: &str) -> Option<u16> {
  let s = s.strip_prefix("0x")?;
  Some(u16::from_str_radix(s, 16).ok()?)
}

fn parse_variable_id(s: &str) -> Variable {
  if let Some(s) = s.strip_prefix('v') {
    if s == "?" {
      return Variable::new(1 << 27, VariableSize::Bit64);
    } else if let Ok(id) = s.parse() {
      return Variable::new(id, VariableSize::Bit64);
    }
  }

  panic!("unknown variable id: {s}");
}
