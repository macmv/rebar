use std::ops::AddAssign;

use rb_codegen::{BlockId, TIndex, TVec};

use crate::analysis::control_flow_graph::ControlFlowGraph;

use super::*;

#[derive(Default)]
pub struct DominatorTree {
  idom: TVec<BlockId, Option<BlockId>>,
  dom:  TVec<BlockId, Vec<BlockId>>,
}

impl DominatorTree {
  pub const ID: AnalysisPassId = AnalysisPassId("dominator_tree");
}

impl AnalysisPass for DominatorTree {
  fn id() -> AnalysisPassId { Self::ID }

  fn pass(&mut self, analysis: &mut Analysis, function: &Function) {
    analysis.load(ControlFlowGraph::ID, function);
    let cfg = analysis.get::<ControlFlowGraph>();

    self.idom = solve(cfg, function.entry());
    self.dom.resize(cfg.len(), vec![]);
    for (child, &parent) in self.idom.enumerate() {
      if let Some(parent) = parent {
        self.dom[parent].push(child);
      }
    }
  }
}

impl DominatorTree {
  pub fn immediate_dominator(&self, block: BlockId) -> Option<BlockId> {
    self.idom.get(block).copied().flatten()
  }

  pub fn direct_dominating(&self, block: BlockId) -> &[BlockId] {
    self
      .dom
      .get(block)
      .map(|v| &v[..])
      .unwrap_or_else(|| panic!("no such block {block:?} in dominator tree"))
  }

  pub fn all_dominating(&self, block: BlockId) -> Vec<BlockId> {
    let mut stack = vec![block];
    let mut dominators = vec![block];
    while let Some(b) = stack.pop() {
      let Some(children) = self.dom.get(b) else { continue };
      dominators.extend(children.iter());
      stack.extend(children);
    }
    dominators
  }

  pub fn is_strict_dominator(&self, dom: BlockId, child: BlockId) -> bool {
    if dom == child {
      return false;
    }

    self.is_dominator(dom, child)
  }

  pub fn is_dominator(&self, dom: BlockId, child: BlockId) -> bool {
    if dom == child {
      return true;
    }

    let mut parent = child;
    while let Some(p) = self.immediate_dominator(parent) {
      if p == dom {
        return true;
      }
      parent = p;
    }

    false
  }

  pub fn preorder(&self) -> Vec<BlockId> {
    let mut out = Vec::new();
    fn walk(u: BlockId, dom: &TVec<BlockId, Vec<BlockId>>, out: &mut Vec<BlockId>) {
      out.push(u);
      if let Some(children) = dom.get(u) {
        for &v in children {
          walk(v, dom, out);
        }
      }
    }
    walk(BlockId::ENTRY, &self.dom, &mut out);
    out
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

    fn edges(dom: &DominatorTree) -> BTreeSet<(BlockId, BlockId)> {
      let mut e = BTreeSet::new();
      for (child, &parent) in dom.idom.enumerate() {
        if let Some(parent) = parent {
          e.insert((parent, child));
        }
      }
      e
    }

    let mut s = String::new();
    s.push_str("digraph CFG {\n");
    s.push_str("  label = \"Dominator Tree\";\n");
    s.push_str("  labelloc = top;\n");
    s.push_str("  graph [fontname=\"Noto Sans\", fontsize=14];\n");
    s.push_str("  node  [shape=box, fontname=\"Noto Sans\", fontsize=10];\n");
    s.push_str("  edge  [fontname=\"Noto Sans\", fontsize=9, arrowsize=0.7];\n");

    for id in 0..self.idom.len() as u32 {
      s.push_str(&format!("  {} [label=\"{:?}\"];\n", id, BlockId::new(id)));
    }
    for (u, v) in edges(self) {
      s.push_str(&format!("  {} -> {};\n", u.as_u32(), v.as_u32()));
    }
    s.push_str("}\n");
    s
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DfsIndex(usize);

impl DfsIndex {
  const ZERO: DfsIndex = DfsIndex(0);
  const MAX: DfsIndex = DfsIndex(usize::MAX);
}

impl AddAssign<usize> for DfsIndex {
  fn add_assign(&mut self, rhs: usize) { self.0 += rhs; }
}

impl<T> TIndex<T> for DfsIndex {
  fn from_index(index: usize) -> Self { DfsIndex(index) }
  fn to_index(self) -> usize { self.0 }
}

struct IDom<'a> {
  cfg: &'a ControlFlowGraph,

  parent:         TVec<DfsIndex, DfsIndex>,
  vertex:         TVec<DfsIndex, BlockId>,
  inverse_vertex: TVec<BlockId, DfsIndex>,

  ancestor: TVec<DfsIndex, DfsIndex>,
  idom:     TVec<DfsIndex, DfsIndex>,
  label:    TVec<DfsIndex, DfsIndex>,
  // A map of nodes to their semidominators.
  semi:     TVec<DfsIndex, DfsIndex>,
}

fn solve(cfg: &ControlFlowGraph, entry: BlockId) -> TVec<BlockId, Option<BlockId>> {
  let mut idom = IDom {
    cfg,

    vertex: TVec::from(vec![BlockId::new(u32::MAX); cfg.len()]),
    parent: TVec::from(vec![DfsIndex::ZERO; cfg.len()]),
    inverse_vertex: TVec::from(vec![DfsIndex::MAX; cfg.len()]),

    semi: TVec::new(),
    idom: TVec::new(),
    ancestor: TVec::new(),
    label: TVec::new(),
  };

  idom.dfs(entry);

  idom.semi = TVec::from((0..idom.reachable()).map(DfsIndex).collect::<Vec<_>>());
  idom.idom = TVec::from(vec![DfsIndex::MAX; idom.reachable()]);
  idom.ancestor = TVec::from(vec![DfsIndex::MAX; idom.reachable()]);
  idom.label = TVec::from((0..idom.reachable()).map(DfsIndex).collect::<Vec<_>>());

  idom.run()
}

impl IDom<'_> {
  const fn reachable(&self) -> usize { self.vertex.as_slice().len() }

  fn to_dfs(&self, b: BlockId) -> Option<DfsIndex> {
    let vert = self.inverse_vertex[b];
    if vert == DfsIndex::MAX { None } else { Some(vert) }
  }

  fn to_block(&self, i: DfsIndex) -> BlockId { self.vertex[i] }

  fn compress(&mut self, v: DfsIndex) {
    if self.ancestor[self.ancestor[v]] != DfsIndex::MAX {
      self.compress(self.ancestor[v]);
      if self.semi[self.label[self.ancestor[v]]] < self.semi[self.label[v]] {
        self.label[v] = self.label[self.ancestor[v]];
      }
      self.ancestor[v] = self.ancestor[self.ancestor[v]];
    }
  }

  fn eval(&mut self, v: DfsIndex) -> DfsIndex {
    if self.ancestor[v] == DfsIndex::MAX {
      return self.label[v];
    }
    self.compress(v);
    self.label[v]
  }

  fn link(&mut self, v: DfsIndex, w: DfsIndex) { self.ancestor[w] = v; }

  fn attach_vertex(&mut self, block: BlockId, dfs: DfsIndex) {
    self.vertex[dfs] = block;
    self.inverse_vertex[block] = dfs;
  }

  /// DFS from `entry`, assigning DFS numbers 0..R to reachable nodes.
  fn dfs(&mut self, entry: BlockId) {
    // iterative stack: (node, next_succ_idx)
    let mut stack: Vec<(BlockId, usize)> = Vec::new();

    let mut time = DfsIndex::ZERO;
    self.attach_vertex(entry, time);
    stack.push((entry, 0));

    while let Some((block, i)) = stack.pop() {
      if i < self.cfg.exits(block).len() {
        let succ = self.cfg.exits(block)[i];
        stack.push((block, i + 1));
        if self.inverse_vertex[succ] == DfsIndex::MAX {
          time += 1;
          self.attach_vertex(succ, time);
          self.parent[time] = self.inverse_vertex[block];
          stack.push((succ, 0));
        }
      }
    }

    // Trim arrays to reachable size R = time
    self.vertex.truncate(time.0 + 1);
    self.parent.truncate(time.0 + 1);
  }

  // This is the Lengauer-Tarjan Dominators Algorithm.
  fn run(mut self) -> TVec<BlockId, Option<BlockId>> {
    if self.reachable() == 1 {
      return TVec::from(vec![None]);
    }

    let mut bucket: TVec<DfsIndex, Vec<DfsIndex>> = TVec::from(vec![vec![]; self.reachable()]);

    // Main LT pass: process in reverse DFS order
    for i in (1..self.reachable()).rev() {
      let i = DfsIndex(i);
      let w = self.vertex[i];

      // 1) Compute semidominator of w
      let mut semi = i;
      for &pred in self.cfg.enters(w) {
        let Some(pred) = self.to_dfs(pred) else { continue };
        let u = self.eval(pred);
        semi = self.semi[u].min(semi);
      }
      self.semi[i] = semi;

      // 2) Add w to bucket of vertex[semi[w]]
      bucket[self.semi[i]].push(i);

      // 3) Link parent of w to w in the ancestor forest
      let parent = self.parent[i];
      self.link(parent, i);

      // 4) For each v in bucket[p], finalize idom[v]
      let mut drained = Vec::new();
      std::mem::swap(&mut drained, &mut bucket[parent]);
      for v in drained {
        let u = self.eval(v);
        if self.semi[u] < self.semi[v] {
          self.idom[v] = u;
        } else {
          self.idom[v] = parent;
        }
      }
    }

    // Second pass: explicitly define idom where necessary
    for i in 1..self.reachable() {
      let i = DfsIndex(i);

      if self.idom[i] != self.semi[i] {
        self.idom[i] = self.idom[self.idom[i]];
      }
    }

    // Convert from DFS index space to block IDs.
    let mut out = TVec::from(vec![None; self.cfg.len()]);

    for i in 1..self.reachable() {
      let i = DfsIndex(i);

      let child_node = self.to_block(i);
      let parent_node = self.to_block(self.idom[i]);
      out[child_node] = Some(parent_node);
    }

    out
  }
}
