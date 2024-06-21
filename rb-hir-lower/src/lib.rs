//! Lowers the AST from rb_syntax into an HIR tree. Performs no type inferrence,
//! and only validates syntax.

use rb_diagnostic::{emit, SourceId, Span};
use rb_hir::ast as hir;
use rb_syntax::{cst, AstNode};

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
  fn span(&self, node: &impl rb_syntax::AstNode) -> Span {
    Span { file: self.source, range: node.syntax().text_range() }
  }

  fn stmt(&mut self, cst: cst::Stmt) -> Option<hir::StmtId> {
    let stmt = match cst {
      cst::Stmt::ExprStmt(expr) => {
        let expr = self.expr_opt(expr.expr(), &expr)?;

        Some(hir::Stmt::Expr(expr))
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    stmt.map(|stmt| self.f.stmts.alloc(stmt))
  }

  fn expr_opt(&mut self, cst: Option<cst::Expr>, parent: &impl AstNode) -> Option<hir::ExprId> {
    match cst {
      Some(expr) => self.expr(expr),
      None => {
        emit!("missing expression", self.span(parent));
        None
      }
    }
  }
  fn expr(&mut self, cst: cst::Expr) -> Option<hir::ExprId> {
    let expr = match cst {
      cst::Expr::Literal(lit) => {
        if let Some(lit) = lit.integer_token() {
          Some(hir::Expr::Literal(hir::Literal::Int(lit.text().parse().unwrap())))
        } else {
          emit!("unexpected literal", self.span(&lit));
          None
        }
      }

      cst::Expr::Name(name) => {
        let name = name.ident_token().unwrap().to_string();

        Some(hir::Expr::Name(name))
      }

      cst::Expr::BinaryExpr(expr) => {
        let lhs = self.expr_opt(expr.lhs(), &expr)?;
        let rhs = self.expr_opt(expr.rhs(), &expr)?;

        let Some(op) = expr.binary_op() else {
          emit!("missing binary operator", self.span(&expr));
          return None;
        };

        let op = if op.plus_token().is_some() {
          hir::BinaryOp::Add
        } else if op.minus_token().is_some() {
          hir::BinaryOp::Sub
        } else {
          emit!("unexpected binary operator", self.span(&expr));
          return None;
        };

        Some(hir::Expr::BinaryOp(lhs, op, rhs))
      }

      cst::Expr::CallExpr(expr) => {
        let lhs = self.expr_opt(expr.expr(), &expr)?;

        let Some(arg_list) = expr.arg_list() else {
          emit!("missing argument list", self.span(&expr));
          return None;
        };

        let mut args = Vec::with_capacity(arg_list.exprs().size_hint().0);
        for arg in arg_list.exprs() {
          args.push(self.expr(arg)?);
        }

        Some(hir::Expr::Call(lhs, args))
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    expr.map(|expr| self.f.exprs.alloc(expr))
  }
}
