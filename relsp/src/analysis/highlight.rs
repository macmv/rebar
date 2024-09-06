use rb_hir::ast as hir;
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

struct Highlighter<'a> {
  func: &'a hir::Function,

  hl: &'a mut Highlight,
}

impl Highlight {
  pub fn from_ast(file: hir::SourceFile) -> Highlight {
    let mut hl = Highlight { tokens: vec![] };

    for (_, func) in file.functions {
      let mut hl = Highlighter { func: &func, hl: &mut hl };
      for stmt in &func.items {
        hl.visit_stmt(*stmt);
      }
    }

    hl
  }
}

impl Highlighter<'_> {
  fn visit_stmt(&mut self, stmt: hir::StmtId) {
    match self.func.stmts[stmt] {
      hir::Stmt::Expr(expr) => self.visit_expr(expr),
      hir::Stmt::Let(_, expr) => self.visit_expr(expr),
      hir::Stmt::Def(_, _, _) => {}
    }
  }

  fn visit_expr(&mut self, expr: hir::ExprId) {
    let expr = &self.func.exprs[expr];

    match expr {
      _ => {}
    }
  }
}

impl HighlightKind {
  pub fn iter() -> impl Iterator<Item = HighlightKind> {
    (0..=HighlightKind::Variable as u8).map(|i| unsafe { std::mem::transmute(i) })
  }
}
