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
        if let Some(lit) = lit.integer_token() {
          hir::Expr::Literal(hir::Literal::Int(lit.text().parse().unwrap()))
        } else if let Some(_) = lit.true_token() {
          hir::Expr::Literal(hir::Literal::Bool(true))
        } else if let Some(_) = lit.false_token() {
          hir::Expr::Literal(hir::Literal::Bool(false))
        } else if let Some(_) = lit.nil_token() {
          hir::Expr::Literal(hir::Literal::Nil)
        } else {
          panic!("unexpected literal {lit}");
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
  macro_rules! ops {
    { $($cst:ident => $hir:ident)* } => {
      $(
        if cst.$cst().is_some() {
          return hir::BinaryOp::$hir;
        }
      )*
    };
  }

  ops! {
    plus_token => Add
    minus_token => Sub
    star_token => Mul
    slash_token => Div
    percent_token => Mod
    eq_eq_token => Eq
    not_eq_token => Neq
    less_token => Lt
    less_eq_token => Lte
    greater_token => Gt
    greater_eq_token => Gte
    and_token => And
    or_token => Or
    bit_and_token => BitAnd
    bit_or_token => BitAnd
  }
  panic!("unexpected binary operator {cst}");
}

fn unary_op_from_cst(cst: &cst::PrefixOp) -> hir::UnaryOp {
  macro_rules! ops {
    { $($cst:ident => $hir:ident)* } => {
      $(
        if cst.$cst().is_some() {
          return hir::UnaryOp::$hir;
        }
      )*
    };
  }

  ops! {
    minus_token => Neg
    bang_token => Not
  }
  panic!("unexpected binary operator {cst}");
}
