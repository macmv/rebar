//! Lowers HIR and the result of typechecking into MIR.

use std::collections::HashMap;

use rb_hir::ast as hir;
use rb_mir::ast as mir;
use rb_typer::{Type, Typer};

pub struct Env {
  pub functions: HashMap<String, mir::NativeFunctionId>,
}

pub fn lower_function(env: &Env, ty: &Typer, hir: &hir::Function) -> mir::Function {
  let mut mir = mir::Function::default();

  let mut lower = Lower { env, ty, hir, mir: &mut mir, locals: HashMap::new() };
  for stmt in hir.items.iter() {
    let id = lower.lower_stmt(*stmt);
    lower.mir.items.push(id);
  }

  mir
}

struct Lower<'a> {
  env: &'a Env,
  ty:  &'a Typer<'a>,
  hir: &'a hir::Function,
  mir: &'a mut mir::Function,

  // TODO: This should be a stack of scopes.
  locals: HashMap<String, mir::VarId>,
}

impl Lower<'_> {
  fn next_var_id(&mut self, ty: Type) -> mir::VarId {
    let id = self.mir.vars.len();
    self.mir.vars.push(ty);
    mir::VarId(id as u32)
  }

  fn lower_stmt(&mut self, stmt: hir::StmtId) -> mir::StmtId {
    let stmt = match self.hir.stmts[stmt] {
      hir::Stmt::Expr(expr) => mir::Stmt::Expr(self.lower_expr(expr)),
      hir::Stmt::Let(ref name, expr) => {
        let mir_expr = self.lower_expr(expr);
        let ty = self.ty.type_of_expr(expr);
        let id = self.next_var_id(ty.clone());
        self.locals.insert(name.clone(), id);
        mir::Stmt::Let(id, ty, mir_expr)
      }
    };

    self.mir.stmts.alloc(stmt)
  }

  fn lower_expr(&mut self, expr: hir::ExprId) -> mir::ExprId {
    let expr = match self.hir.exprs[expr] {
      hir::Expr::Literal(hir::Literal::Int(v)) => mir::Expr::Literal(mir::Literal::Int(v)),

      // HIR should have fully qualified names, and the typer should get the type of this name.
      // We should probably convert it to something more useful than a string though.
      hir::Expr::Name(ref v) => match self.locals.get(v) {
        Some(local) => mir::Expr::Local(*local),
        None => {
          let id = self.env.functions[v];
          mir::Expr::Native(id, self.ty.type_of_expr(expr))
        }
      },

      hir::Expr::Block(ref block) => {
        let mut stmts = vec![];

        // FIXME: Make a new scope here so that local variables are local to blocks.
        for stmt in block.iter() {
          let stmt = self.lower_stmt(*stmt);
          stmts.push(stmt);
        }

        mir::Expr::Block(stmts)
      }

      hir::Expr::Paren(inner) => return self.lower_expr(inner),

      hir::Expr::UnaryOp(inner, ref op) => {
        let inner = self.lower_expr(inner);

        let op = match op {
          hir::UnaryOp::Not => mir::UnaryOp::Not,
          hir::UnaryOp::Neg => mir::UnaryOp::Neg,
        };

        mir::Expr::Unary(inner, op, self.ty.type_of_expr(expr))
      }

      hir::Expr::BinaryOp(lhs, ref op, rhs) => {
        let lhs = self.lower_expr(lhs);
        let rhs = self.lower_expr(rhs);

        // TODO: There might be some things like signed comparisons that should be
        // different in the MIR tree? Not sure if these need to be distinct
        // types.
        let op = match op {
          hir::BinaryOp::Add => mir::BinaryOp::Add,
          hir::BinaryOp::Sub => mir::BinaryOp::Sub,
          hir::BinaryOp::Mul => mir::BinaryOp::Mul,
          hir::BinaryOp::Div => mir::BinaryOp::Div,
          hir::BinaryOp::Mod => mir::BinaryOp::Mod,
          hir::BinaryOp::BitAnd => mir::BinaryOp::BitAnd,
          hir::BinaryOp::BitOr => mir::BinaryOp::BitOr,
          hir::BinaryOp::And => mir::BinaryOp::And,
          hir::BinaryOp::Or => mir::BinaryOp::Or,
          hir::BinaryOp::Eq => mir::BinaryOp::Eq,
          hir::BinaryOp::Neq => mir::BinaryOp::Neq,
          hir::BinaryOp::Lt => mir::BinaryOp::Lt,
          hir::BinaryOp::Lte => mir::BinaryOp::Lte,
          hir::BinaryOp::Gt => mir::BinaryOp::Gt,
          hir::BinaryOp::Gte => mir::BinaryOp::Gte,
        };

        mir::Expr::Binary(lhs, op, rhs, self.ty.type_of_expr(expr))
      }

      hir::Expr::Call(lhs, ref args) => {
        let lhs_ty = self.ty.type_of_expr(lhs);
        let lhs = self.lower_expr(lhs);
        let args = args.iter().map(|&arg| self.lower_expr(arg)).collect();

        mir::Expr::Call(lhs, lhs_ty, args)
      }

      hir::Expr::If { cond, then, els } => {
        let cond = self.lower_expr(cond);
        let then = self.lower_expr(then);
        let els = els.map(|e| self.lower_expr(e));

        mir::Expr::If { cond, then, els }
      }

      ref v => unimplemented!("lowering expression {v:?}"),
    };

    self.mir.exprs.alloc(expr)
  }
}
