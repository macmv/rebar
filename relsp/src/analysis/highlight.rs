use crate::files::FileId;
use rb_syntax::TextRange;

#[derive(Debug, Clone)]
pub struct Highlight {
  pub tokens: Vec<HighlightToken>,
}

#[derive(Debug, Clone)]
pub struct HighlightToken {
  pub range:      TextRange,
  pub kind:       HighlightKind,
  pub modifierst: u32,
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum HighlightKind {
  /// Function calls and definitions.
  Function,

  /// Keywords like `struct` or `def`.
  Keyword,

  /// Number literals.
  Number,

  // String literals.
  String,

  /// Parameters in function definitions, like the `x` in `def foo(x: int)`.
  Parameter,

  /// Type references, like the `int` in `let x: int = 92` or `def foo(x: int)`.
  Type,

  /// Local variables.
  // Keep last!
  Variable,
}

struct Highlighter {
  file: FileId,

  hl: Highlight,
}

impl Highlight {
  pub fn from_ast(file: FileId) -> Highlight {
    let hl = Highlighter::new(file);

    // TODO: Walk the AST and collect highlights.

    hl.hl
  }
}

impl Highlighter {
  pub fn new(file: FileId) -> Self { Highlighter { file, hl: Highlight { tokens: vec![] } } }
}

impl HighlightKind {
  pub fn iter() -> impl Iterator<Item = HighlightKind> {
    (0..=HighlightKind::Variable as u8).map(|i| unsafe { std::mem::transmute(i) })
  }
}
