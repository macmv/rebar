//! Lowers HIR and the result of typechecking into MIR.

use rb_hir::ast as hir;
use rb_mir::ast as mir;
use rb_typer::Typer;

pub fn lower_function(ty: &Typer, hir: &hir::Function) -> mir::Function {
  let mut mir = mir::Function::default();

  let mut lower = Lower { ty, hir, mir: &mut mir };
  for stmt in hir.items.iter() {
    let id = lower.lower_stmt(*stmt);
    lower.mir.items.push(id);
  }

  mir
}

struct Lower<'a> {
  ty:  &'a Typer<'a>,
  hir: &'a hir::Function,
  mir: &'a mut mir::Function,
}

impl Lower<'_> {
  fn lower_stmt(&mut self, stmt: hir::StmtId) -> mir::StmtId {
    let stmt = match self.hir.stmts[stmt] {
      hir::Stmt::Expr(expr) => mir::Stmt::Expr(self.lower_expr(expr)),
    };

    self.mir.stmts.alloc(stmt)
  }

  fn lower_expr(&mut self, expr: hir::ExprId) -> mir::ExprId {
    let expr = match self.hir.exprs[expr] {
      hir::Expr::Literal(hir::Literal::Int(v)) => mir::Expr::Literal(mir::Literal::Int(v)),

      // Uhhhhhhhhhhhhhhhhh
      //
      // HIR should have fully qualified names, and the typer should get the type of this name.
      // We should probably convert it to something more useful than a string though.
      hir::Expr::Name(ref v) => mir::Expr::Name(v.clone(), self.ty.type_of_expr(expr)),

      hir::Expr::BinaryOp(lhs, ref op, rhs) => {
        let lhs = self.lower_expr(lhs);
        let rhs = self.lower_expr(rhs);

        let op = match op {
          hir::BinaryOp::Add => mir::BinaryOp::Add,
          hir::BinaryOp::Sub => mir::BinaryOp::Sub,
          hir::BinaryOp::Mul => mir::BinaryOp::Mul,
          hir::BinaryOp::Div => mir::BinaryOp::Div,
          _ => todo!(),
        };

        mir::Expr::Binary(lhs, op, rhs, self.ty.type_of_expr(expr))
      }

      hir::Expr::Call(lhs, ref args) => {
        let lhs = self.lower_expr(lhs);
        let args = args.iter().map(|&arg| self.lower_expr(arg)).collect();

        mir::Expr::Call(lhs, args)
      }

      ref v => unimplemented!("lowering expression {v:?}"),
    };

    self.mir.exprs.alloc(expr)
  }
}
