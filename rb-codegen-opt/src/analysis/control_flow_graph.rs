use rb_codegen::{BlockId, Opcode, TVec, TerminatorInstruction};

use super::*;

#[derive(Default)]
pub struct ControlFlowGraph {
  blocks: TVec<BlockId, ControlFlowBlock>,
}

#[derive(Clone)]
struct ControlFlowBlock {
  enters: Vec<BlockId>,
  exits:  Vec<BlockId>,
}

impl ControlFlowGraph {
  pub const ID: AnalysisPassId = AnalysisPassId("control_flow_graph");
}

impl AnalysisPass for ControlFlowGraph {
  fn id() -> AnalysisPassId { Self::ID }

  fn pass(&mut self, _: &mut Analysis, function: &Function) {
    self.blocks = TVec::from(vec![
      const { ControlFlowBlock { enters: vec![], exits: vec![] } };
      function.blocks.len()
    ]);

    for (id, block) in function.blocks.iter().enumerate() {
      let id = BlockId::new(id as u32);
      for instr in &block.instructions {
        if let Opcode::Branch(_, target) = instr.opcode {
          self.add_jump(id, target);
        }
      }

      if let TerminatorInstruction::Jump(target) = block.terminator {
        self.add_jump(id, target);
      }
    }
  }
}

impl ControlFlowGraph {
  fn add_jump(&mut self, from: BlockId, to: BlockId) {
    self.blocks[from].exits.push(to);
    self.blocks[to].enters.push(from);
  }

  pub fn len(&self) -> usize { self.blocks.len() }

  #[track_caller]
  pub fn enters(&self, block: BlockId) -> &[BlockId] {
    match self.blocks.get(block) {
      Some(b) => &b.enters,
      None => panic!("no such block {block:?}"),
    }
  }

  #[track_caller]
  pub fn exits(&self, block: BlockId) -> &[BlockId] {
    match self.blocks.get(block) {
      Some(b) => &b.exits,
      None => panic!("no such block {block:?}"),
    }
  }

  #[allow(unused)]
  pub fn show_graph(&self) {
    use std::{io::Write, process::Command};

    let mut cmd =
      Command::new("xdot").arg("-").stdin(std::process::Stdio::piped()).spawn().unwrap();

    cmd.stdin.take().unwrap().write_all(self.make_graph().as_bytes()).unwrap();
  }

  #[allow(unused)]
  fn make_graph(&self) -> String {
    use std::collections::BTreeSet;

    fn edges(cfg: &ControlFlowGraph) -> BTreeSet<(BlockId, BlockId)> {
      let mut e = BTreeSet::new();
      for (i, b) in cfg.blocks.iter().enumerate() {
        let from = BlockId::new(i as u32);
        for &to in &b.exits {
          e.insert((from, to));
        }
      }
      e
    }

    let mut s = String::new();
    s.push_str("digraph CFG {\n");
    s.push_str("  label = \"Control Flow Graph\";\n");
    s.push_str("  labelloc = top;\n");
    s.push_str("  graph [fontname=\"Noto Sans\", fontsize=14];\n");
    s.push_str("  node  [shape=box, fontname=\"Noto Sans\", fontsize=10];\n");
    s.push_str("  edge  [fontname=\"Noto Sans\", fontsize=9, arrowsize=0.7];\n");

    for id in 0..self.blocks.len() as u32 {
      s.push_str(&format!("  {} [label=\"{:?}\"];\n", id, BlockId::new(id)));
    }
    for (u, v) in edges(self) {
      s.push_str(&format!("  {} -> {};\n", u.as_u32(), v.as_u32()));
    }
    s.push_str("}\n");
    s
  }
}
