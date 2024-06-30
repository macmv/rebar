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

macro_rules! match_token {
  {
    match $id:ident {
      $($cst:ident($pat:pat) => $hir:expr,)*
    }
  } => {
    $(
      if let Some($pat) = $id.$cst() {
        $hir
      } else
    )* {
      panic!("unexpected token {}", $id)
    }
  };
}

impl FunctionLower<'_> {
  fn stmt(&mut self, cst: cst::Stmt) -> hir::StmtId {
    let stmt = match cst {
      cst::Stmt::ExprStmt(ref expr) => {
        let expr = self.expr_opt(expr.expr());

        hir::Stmt::Expr(expr)
      }

      cst::Stmt::Let(ref let_stmt) => {
        let name = let_stmt.ident_token().unwrap().to_string();
        let expr = self.expr_opt(let_stmt.expr());

        hir::Stmt::Let(name, expr)
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
        match_token! {
          match lit {
            integer_token(lit) => hir::Expr::Literal(hir::Literal::Int(lit.text().parse().unwrap())),
            true_token(_) => hir::Expr::Literal(hir::Literal::Bool(true)),
            false_token(_) => hir::Expr::Literal(hir::Literal::Bool(false)),
            nil_token(_) => hir::Expr::Literal(hir::Literal::Nil),
          }
        }
      }

      cst::Expr::Name(ref name) => {
        let name = name.ident_token().unwrap().to_string();

        hir::Expr::Name(name)
      }

      cst::Expr::Block(ref block) => {
        let mut stmts = vec![];
        for stmt in block.stmts() {
          stmts.push(self.stmt(stmt));
        }
        hir::Expr::Block(stmts)
      }

      cst::Expr::ParenExpr(ref expr) => {
        let expr = self.expr_opt(expr.expr());
        hir::Expr::Paren(expr)
      }

      cst::Expr::PrefixExpr(ref expr) => {
        let rhs = self.expr_opt(expr.expr());

        let op = unary_op_from_cst(&expr.prefix_op().unwrap());

        hir::Expr::UnaryOp(rhs, op)
      }

      cst::Expr::BinaryExpr(ref expr) => {
        let lhs = self.expr_opt(expr.lhs());
        let rhs = self.expr_opt(expr.rhs());

        let op = binary_op_from_cst(&expr.binary_op().unwrap());

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

      cst::Expr::IfExpr(ref expr) => hir::Expr::If {
        cond: self.expr_opt(expr.cond()),
        then: self.expr_opt(expr.then()),
        els:  expr.els().map(|e| self.expr(e)),
      },

      _ => unimplemented!("lowering for {:?}", cst),
    };

    self.span_map.exprs.push(Span { file: self.source, range: cst.syntax().text_range() });
    self.f.exprs.alloc(expr)
  }
}

fn binary_op_from_cst(cst: &cst::BinaryOp) -> hir::BinaryOp {
  use hir::BinaryOp::*;

  match_token! {
    match cst {
      plus_token(_) => Add,
      minus_token(_) => Sub,
      star_token(_) => Mul,
      slash_token(_) => Div,
      percent_token(_) => Mod,
      eq_eq_token(_) => Eq,
      not_eq_token(_) => Neq,
      less_token(_) => Lt,
      less_eq_token(_) => Lte,
      greater_token(_) => Gt,
      greater_eq_token(_) => Gte,
      and_token(_) => And,
      or_token(_) => Or,
      bit_and_token(_) => BitAnd,
      bit_or_token(_) => BitAnd,
    }
  }
}

fn unary_op_from_cst(cst: &cst::PrefixOp) -> hir::UnaryOp {
  use hir::UnaryOp::*;

  match_token! {
    match cst {
      minus_token(_) => Neg,
      bang_token(_) => Not,
    }
  }
}
