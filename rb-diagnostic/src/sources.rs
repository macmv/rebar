use la_arena::{Arena, Idx};
use line_index::LineIndex;

pub type SourceId = Idx<Source>;

pub struct Sources {
  sources: Arena<Source>,
}

pub struct Source {
  pub source:     String,
  pub line_index: LineIndex,
}

impl Source {
  fn new(source: String) -> Self { Source { line_index: LineIndex::new(&source), source } }
}

impl Sources {
  pub fn new() -> Self { Self { sources: Arena::new() } }

  pub fn add(&mut self, source: String) -> SourceId { self.sources.alloc(Source::new(source)) }
}
