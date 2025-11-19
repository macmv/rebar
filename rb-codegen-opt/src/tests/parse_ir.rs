use rb_codegen::{
  Block, BlockId, ExternId, Function, FunctionId, Instruction, InstructionInput, InstructionOutput,
  Math, Opcode, Phi, Variable, VariableSize,
};
use smallvec::SmallVec;

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
  let mut function = Function::default();

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

    let (first_word, mut args) = line.split_once(' ').unwrap_or((line, ""));
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
      "compare(eq)" => Opcode::Compare(rb_codegen::Condition::Equal),
      "compare(ne)" => Opcode::Compare(rb_codegen::Condition::NotEqual),
      "compare(gt)" => Opcode::Compare(rb_codegen::Condition::Greater),
      "compare(lt)" => Opcode::Compare(rb_codegen::Condition::Less),
      "compare(ge)" => Opcode::Compare(rb_codegen::Condition::GreaterEqual),
      "compare(le)" => Opcode::Compare(rb_codegen::Condition::LessEqual),
      "syscall" => Opcode::Syscall,

      "call" => {
        let (_func, rest) = args.split_once(' ').unwrap();
        args = rest;

        if _func.starts_with("extern") {
          Opcode::CallExtern(ExternId(0))
        } else {
          Opcode::Call(FunctionId::new(0))
        }
      }

      "jump" => {
        let args = args.strip_prefix("to block ").unwrap();
        let target = args.parse::<u32>().unwrap();

        function.blocks.last_mut().unwrap().terminator =
          rb_codegen::TerminatorInstruction::Jump(BlockId::new(target));
        continue;
      }

      "return" => {
        let mut rets = smallvec![];
        for ret in args.split(',') {
          let ret = ret.trim();
          if ret.is_empty() {
            continue;
          }

          let var = parse_variable_id(ret).unwrap();
          rets.push(InstructionInput::Var(var));
        }

        function.blocks.last_mut().unwrap().terminator =
          rb_codegen::TerminatorInstruction::Return(rets);
        continue;
      }

      "trap" => {
        function.blocks.last_mut().unwrap().terminator = rb_codegen::TerminatorInstruction::Trap;
        continue;
      }

      _ if line.contains("phi") => {
        function.blocks.last_mut().unwrap().phis.push(parse_phi(line));
        continue;
      }

      _ => panic!("unknown instruction: {line}"),
    };

    let mut input: SmallVec<[InstructionInput; 2]> = smallvec![];
    let mut output: SmallVec<[InstructionOutput; 2]> = smallvec![];

    let mut in_input = false;
    for mut item in args.split(' ') {
      match item.trim() {
        "" => continue,
        "=" => {
          in_input = true;
          continue;
        }
        _ => {}
      }

      if let Some(v) = item.strip_suffix(',') {
        item = v;
      }

      if let Some(v) = parse_variable_id(item) {
        if in_input {
          input.push(v.into());
        } else {
          output.push(v.into());
        }
      } else if in_input && let Some(imm) = parse_hex(item) {
        input.push(imm.into());
      } else {
        panic!("unknown argument: {item}");
      }
    }

    function.blocks.last_mut().unwrap().instructions.push(Instruction { opcode, input, output });
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

      (block, Some(parse_variable_id(rhs).unwrap()))
    })
    .collect();

  Phi { to: parse_variable_id(to.trim()).unwrap(), from: ids }
}

fn parse_hex(s: &str) -> Option<u64> {
  let s = s.strip_prefix("0x")?;
  Some(u64::from_str_radix(s, 16).ok()?)
}

fn parse_variable_id(s: &str) -> Option<Variable> {
  let size = match s.chars().next() {
    Some('r') => VariableSize::Bit64,
    Some('e') => VariableSize::Bit32,
    Some('x') => VariableSize::Bit16,
    Some('l') => VariableSize::Bit8,
    Some('b') => VariableSize::Bit1,
    _ => return None,
  };

  let id = s[1..].parse::<u32>().ok()?;
  Some(Variable::new(id, size))
}
