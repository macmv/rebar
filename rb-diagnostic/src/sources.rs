use la_arena::{Arena, Idx};

pub type SourceId = Idx<Source>;

pub struct Sources {
  sources: Arena<Source>,
}

pub struct Source {
  source: String,
}

impl Sources {
  pub fn new() -> Self { Self { sources: Arena::new() } }

  pub fn add(&mut self, source: String) -> SourceId { self.sources.alloc(Source { source }) }
}
