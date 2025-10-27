use rb_hir::{ast as hir, FunctionSpanMap, ModuleSpanMap};
use rb_hir_lower::AstIdMap;
use rb_syntax::{
  cst, AstNode, NodeOrToken, Parse, SyntaxKind::*, SyntaxNodePtr, TextRange, TextSize,
};

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

  /// Comments.
  Comment,

  /// Local variables.
  // Keep last!
  Variable,
}

struct Highlighter<'a> {
  func:       &'a hir::Function,
  span_map:   &'a FunctionSpanMap,
  ast_id_map: &'a AstIdMap,

  hl: &'a mut Highlight,
}

impl Highlight {
  pub fn from_ast(
    cst: Parse<cst::SourceFile>,
    file: hir::Module,
    span_map: &ModuleSpanMap,
    ast_id_maps: &[AstIdMap],
  ) -> Highlight {
    let mut hl = Highlight { tokens: vec![] };

    for child in cst.syntax_node().descendants_with_tokens() {
      match child {
        NodeOrToken::Token(t) => match t.kind() {
          WHITESPACE if t.text().trim_start().starts_with("//") => {
            let mut line_start = None;
            let mut prev = '\n';
            let mut offset = 0;

            let mut add_token = |line_start: &mut Option<usize>, offset: usize| {
              if let Some(start) = line_start.take() {
                hl.tokens.push(HighlightToken {
                  range:      TextRange::new(
                    t.text_range().start() + TextSize::from(start as u32),
                    t.text_range().end() + TextSize::from(offset as u32),
                  ),
                  kind:       HighlightKind::Comment,
                  modifierst: 0,
                });
              }
            };

            for c in t.text().chars() {
              if prev == '/' && c == '/' {
                line_start = Some(offset - 1);
                add_token(&mut line_start, offset);
              }

              prev = c;
              offset += c.len_utf8();
            }

            add_token(&mut line_start, offset);
          }

          // TODO: This is wrong, it should be in the same block as above, as multiple types of
          // comments in a row will form a single whitespace token.
          WHITESPACE if t.text().trim_start().starts_with("/*") => {
            hl.tokens.push(HighlightToken {
              range:      t.text_range(),
              kind:       HighlightKind::Comment,
              modifierst: 0,
            });
          }

          _ => {}
        },
        NodeOrToken::Node(n) => {
          let mut hl = Highlighter {
            func:       &file.functions[file.main_function.unwrap()],
            span_map:   &span_map.functions[&file.main_function.unwrap()],
            ast_id_map: &ast_id_maps[file.main_function.unwrap().into_raw().into_u32() as usize],
            hl:         &mut hl,
          };

          if cst::Expr::can_cast(n.kind()) {
            if let Some(id) = hl.ast_id_map.exprs.get(&SyntaxNodePtr::new(&n)) {
              hl.visit_expr(*id);
            }
          } else if cst::Stmt::can_cast(n.kind()) {
            if let Some(id) = hl.ast_id_map.stmts.get(&SyntaxNodePtr::new(&n)) {
              hl.visit_stmt(*id);
            }
          }
        }
      }
    }

    /*
    for (i, func) in file.functions.values().enumerate() {
      let mut hl = Highlighter { func: &func, span_map: &span_maps[i], hl: &mut hl };
      for stmt in &func.items {
        hl.visit_stmt(*stmt);
      }
    }
    */

    hl.tokens.sort_unstable_by_key(|t| t.range.start());

    hl
  }
}

impl Highlighter<'_> {
  fn visit_stmt(&mut self, stmt: hir::StmtId) {
    if let hir::Stmt::Let(_, _) = self.func.stmts[stmt] {
      let span = self.span_map.let_stmts[&stmt];
      self.hl.tokens.push(HighlightToken {
        range:      span.range,
        kind:       HighlightKind::Keyword,
        modifierst: 0,
      });
    }
  }

  fn visit_expr(&mut self, expr: hir::ExprId) {
    match self.func.exprs[expr] {
      hir::Expr::Literal(hir::Literal::Nil) => self.token(expr, HighlightKind::Number),
      hir::Expr::Literal(hir::Literal::Int(_)) => self.token(expr, HighlightKind::Number),
      hir::Expr::Literal(hir::Literal::Bool(_)) => self.token(expr, HighlightKind::Number),
      hir::Expr::String(_) => self.token(expr, HighlightKind::String),

      // TODO: Name resolution.
      hir::Expr::Name(_) => self.token(expr, HighlightKind::Variable),

      hir::Expr::Call(lhs, _) => self.token(lhs, HighlightKind::Function),

      hir::Expr::BinaryOp(_, _, _) => {
        let span = self.span_map.binary_ops[&expr];
        self.hl.tokens.push(HighlightToken {
          range:      span.range,
          kind:       HighlightKind::Operator,
          modifierst: 0,
        });
      }
      hir::Expr::UnaryOp(_, _) => {
        let span = self.span_map.unary_ops[&expr];
        self.hl.tokens.push(HighlightToken {
          range:      span.range,
          kind:       HighlightKind::Operator,
          modifierst: 0,
        });
      }

      hir::Expr::If { .. } => {
        let (if_span, els_span) = self.span_map.if_exprs[&expr];
        self.hl.tokens.push(HighlightToken {
          range:      if_span.range,
          kind:       HighlightKind::Keyword,
          modifierst: 0,
        });

        if let Some(els) = els_span {
          self.hl.tokens.push(HighlightToken {
            range:      els.range,
            kind:       HighlightKind::Keyword,
            modifierst: 0,
          });
        }
      }

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
