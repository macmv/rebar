//! Lowers the AST from rb_syntax into an HIR tree. Performs no type inferrence,
//! and only validates syntax.

use rb_diagnostic::{SourceId, Span};
use rb_hir::{ast as hir, SpanMap};
use rb_syntax::{cst, AstNode};

pub fn lower_source(cst: cst::SourceFile, source: SourceId) -> (hir::SourceFile, SpanMap) {
  let mut out = hir::SourceFile::default();
  let mut main = hir::Function::default();
  let mut span_map = SpanMap::default();

  let mut lower = FunctionLower { source, f: &mut main, span_map: &mut span_map };
  for stmt in cst.stmts() {
    let item = lower.stmt(stmt);
    lower.f.items.push(item);
  }

  out.main_function = Some(out.functions.alloc(main));
  (out, span_map)
}

struct FunctionLower<'a> {
  source:   SourceId,
  f:        &'a mut hir::Function,
  span_map: &'a mut SpanMap,
}

impl FunctionLower<'_> {
  fn stmt(&mut self, cst: cst::Stmt) -> hir::StmtId {
    let stmt = match cst {
      cst::Stmt::ExprStmt(ref expr) => {
        let expr = self.expr_opt(expr.expr());

        hir::Stmt::Expr(expr)
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    self.span_map.stmts.push(Span { file: self.source, range: cst.syntax().text_range() });
    self.f.stmts.alloc(stmt)
  }

  fn expr_opt(&mut self, cst: Option<cst::Expr>) -> hir::ExprId {
    match cst {
      Some(expr) => self.expr(expr),
      None => panic!("missing expression"),
    }
  }
  fn expr(&mut self, cst: cst::Expr) -> hir::ExprId {
    let expr = match cst {
      cst::Expr::Literal(ref lit) => {
        if let Some(lit) = lit.integer_token() {
          hir::Expr::Literal(hir::Literal::Int(lit.text().parse().unwrap()))
        } else {
          panic!("unexpected literal {lit}");
        }
      }

      cst::Expr::Name(ref name) => {
        let name = name.ident_token().unwrap().to_string();

        hir::Expr::Name(name)
      }

      cst::Expr::BinaryExpr(ref expr) => {
        let lhs = self.expr_opt(expr.lhs());
        let rhs = self.expr_opt(expr.rhs());

        let Some(op) = expr.binary_op() else {
          panic!("missing binary operator {expr}");
        };

        let op = if op.plus_token().is_some() {
          hir::BinaryOp::Add
        } else if op.minus_token().is_some() {
          hir::BinaryOp::Sub
        } else if op.star_token().is_some() {
          hir::BinaryOp::Mul
        } else if op.slash_token().is_some() {
          hir::BinaryOp::Div
        } else {
          panic!("unexpected binary operator {expr}");
        };

        hir::Expr::BinaryOp(lhs, op, rhs)
      }

      cst::Expr::CallExpr(ref expr) => {
        let lhs = self.expr_opt(expr.expr());

        let Some(arg_list) = expr.arg_list() else {
          panic!("missing argument list {expr}");
        };

        let mut args = Vec::with_capacity(arg_list.exprs().size_hint().0);
        for arg in arg_list.exprs() {
          args.push(self.expr(arg));
        }

        hir::Expr::Call(lhs, args)
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    self.span_map.exprs.push(Span { file: self.source, range: cst.syntax().text_range() });
    self.f.exprs.alloc(expr)
  }
}
