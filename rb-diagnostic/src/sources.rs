use std::ops::Index;

use la_arena::{Arena, Idx};
use line_index::LineIndex;

pub type SourceId = Idx<Source>;

pub struct Sources {
  sources: Arena<Source>,
}

pub struct Source {
  pub source:     String,
  pub name:       String,
  pub line_index: LineIndex,
}

impl Source {
  pub fn new(name: String, source: String) -> Self {
    Source { line_index: LineIndex::new(&source), source, name }
  }
}

impl Default for Sources {
  fn default() -> Self { Self::new() }
}

impl Sources {
  pub fn new() -> Self { Self { sources: Arena::new() } }

  pub fn add(&mut self, source: Source) -> SourceId { self.sources.alloc(source) }
  pub fn get(&self, id: SourceId) -> &Source { &self.sources[id] }
}

impl Index<SourceId> for Sources {
  type Output = Source;

  fn index(&self, index: SourceId) -> &Self::Output { &self.sources[index] }
}
