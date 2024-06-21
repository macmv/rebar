//! Lowers the AST from rb_syntax into an HIR tree. Performs no type inferrence,
//! and only validates syntax.

use rb_diagnostic::{emit, SourceId, Span};
use rb_hir::ast as hir;
use rb_syntax::cst;

pub fn lower_source(cst: cst::SourceFile, source: SourceId) -> hir::SourceFile {
  let mut out = hir::SourceFile::default();
  let mut main = hir::Function::default();

  let mut lower = FunctionLower { f: &mut main, source };
  for stmt in cst.stmts() {
    match lower.stmt(stmt) {
      Some(i) => lower.f.items.push(i),
      None => {}
    }
  }

  out.main_function = Some(out.functions.alloc(main));
  out
}

struct FunctionLower<'a> {
  source: SourceId,
  f:      &'a mut hir::Function,
}

impl FunctionLower<'_> {
  fn span(&self, node: impl rb_syntax::AstNode) -> Span {
    Span { file: self.source, range: node.syntax().text_range() }
  }

  fn stmt(&mut self, cst: cst::Stmt) -> Option<hir::StmtId> {
    let stmt = match cst {
      cst::Stmt::ExprStmt(expr) => {
        let Some(expr) = expr.expr() else {
          emit!("missing expression", self.span(expr));
          return None;
        };
        let expr = self.expr(expr)?;

        Some(hir::Stmt::Expr(expr))
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    stmt.map(|stmt| self.f.stmts.alloc(stmt))
  }

  fn expr(&mut self, cst: cst::Expr) -> Option<hir::ExprId> {
    let expr = match cst {
      cst::Expr::Literal(lit) => {
        if let Some(lit) = lit.integer_token() {
          Some(hir::Expr::Literal(hir::Literal::Int(lit.text().parse().unwrap())))
        } else {
          emit!("unexpected literal", self.span(lit));
          None
        }
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    expr.map(|expr| self.f.exprs.alloc(expr))
  }
}
