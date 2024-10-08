use rb_hir::{ast as hir, SpanMap};
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

  /// Operators like `+` or `==`.
  Operator,

  /// String literals.
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
  func:     &'a hir::Function,
  span_map: &'a SpanMap,

  hl: &'a mut Highlight,
}

impl Highlight {
  pub fn from_ast(file: hir::SourceFile, span_map: &SpanMap) -> Highlight {
    let mut hl = Highlight { tokens: vec![] };

    for (_, func) in file.functions {
      let mut hl = Highlighter { func: &func, span_map, hl: &mut hl };
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
    match self.func.exprs[expr] {
      hir::Expr::Literal(hir::Literal::Nil) => self.token(expr, HighlightKind::Number),
      hir::Expr::Literal(hir::Literal::Int(_)) => self.token(expr, HighlightKind::Number),
      hir::Expr::Literal(hir::Literal::Bool(_)) => self.token(expr, HighlightKind::Number),
      hir::Expr::Literal(hir::Literal::String(_)) => self.token(expr, HighlightKind::String),

      hir::Expr::StringInterp(ref segments) => {
        for s in segments {
          match s {
            hir::StringInterp::Literal(_) => self.token(expr, HighlightKind::String),
            hir::StringInterp::Expr(expr) => self.visit_expr(*expr),
          }
        }
      }

      hir::Expr::Call(lhs, ref args) => {
        self.token(lhs, HighlightKind::Function);

        for &arg in args {
          self.visit_expr(arg);
        }
      }

      hir::Expr::BinaryOp(lhs, _, rhs) => {
        self.visit_expr(lhs);

        let span = self.span_map.binary_ops[&expr];
        self.hl.tokens.push(HighlightToken {
          range:      span.range,
          kind:       HighlightKind::Operator,
          modifierst: 0,
        });

        self.visit_expr(rhs);
      }
      hir::Expr::UnaryOp(inner, _) => {
        // TODO: Figure out if this is a prefix or postfix operator.
        let span = self.span_map.unary_ops[&expr];
        self.hl.tokens.push(HighlightToken {
          range:      span.range,
          kind:       HighlightKind::Operator,
          modifierst: 0,
        });

        self.visit_expr(inner);
      }
      hir::Expr::Paren(expr) => self.visit_expr(expr),

      _ => {}
    }
  }

  fn token(&mut self, id: hir::ExprId, kind: HighlightKind) {
    let span = self.span_map.exprs[u32::from(id.into_raw()) as usize];
    self.hl.tokens.push(HighlightToken { range: span.range, kind, modifierst: 0 });
  }
}

impl HighlightKind {
  pub fn iter() -> impl Iterator<Item = HighlightKind> {
    (0..=HighlightKind::Variable as u8).map(|i| unsafe { std::mem::transmute(i) })
  }
}
