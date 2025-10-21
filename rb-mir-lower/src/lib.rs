//! Lowers HIR and the result of typechecking into MIR.

use std::collections::HashMap;

use rb_hir::ast as hir;
use rb_mir::{
  ast::{self as mir, UserFunctionId},
  MirContext,
};
use rb_typer::{Type, Typer};

/// The environment for lowering to MIR. This stores a tree of namespaces to
/// native IDs, that are stored directly in the MIR.
pub struct Env<'a> {
  pub ctx:   &'a MirContext,
  pub items: HashMap<String, Item>,
}

pub enum Item {
  NativeFunction(mir::NativeFunctionId),
  UserFunction(UserFunction),
}

pub struct UserFunction {
  pub id:        UserFunctionId,
  pub intrinsic: Option<mir::Intrinsic>,
}

impl Env<'_> {
  pub fn declare_user_function(&mut self, id: u64, function: &hir::Function) {
    let mut func = UserFunction { id: UserFunctionId(id), intrinsic: None };

    for attr in &function.attrs {
      if attr.path == "rebar::intrinsic" {
        func.intrinsic = Some(mir::Intrinsic::Syscall);
      }
    }

    self.items.insert(function.name.clone(), Item::UserFunction(func));
  }
}

pub fn lower_function(env: &Env, ty: &Typer, hir: &hir::Function) -> mir::Function {
  let mut mir = mir::Function::default();

  let mut lower = Lower { env, ty, hir, mir: &mut mir, locals: HashMap::new() };

  for (name, te) in hir.args.iter() {
    let ty = rb_typer::type_of_type_expr(te);

    lower.mir.params.push(ty.clone());
    let id = lower.next_var_id(ty);
    lower.locals.insert(name.clone(), id);
  }

  if let Some(ret) = &hir.ret {
    lower.mir.ret = Some(rb_typer::type_of_type_expr(ret));
  }

  for stmt in hir.items.iter() {
    if let Some(stmt) = lower.lower_stmt(*stmt) {
      lower.mir.items.push(stmt);
    }
  }

  mir
}

struct Lower<'a> {
  env: &'a Env<'a>,
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

  fn lower_stmt(&mut self, stmt: hir::StmtId) -> Option<mir::StmtId> {
    let stmt = match self.hir.stmts[stmt] {
      hir::Stmt::Expr(expr) => mir::Stmt::Expr(self.lower_expr(expr)),
      hir::Stmt::Let(ref name, expr) => {
        let mir_expr = self.lower_expr(expr);
        let ty = self.ty.type_of_expr(expr);
        let id = self.next_var_id(ty.clone());
        self.locals.insert(name.clone(), id);
        mir::Stmt::Let(id, ty, mir_expr)
      }
      hir::Stmt::FunctionDef(_) | hir::Stmt::Struct => return None,
    };

    Some(self.mir.stmts.alloc(stmt))
  }

  fn lower_expr(&mut self, expr: hir::ExprId) -> mir::ExprId {
    let expr = match self.hir.exprs[expr] {
      hir::Expr::Literal(hir::Literal::Nil) => mir::Expr::Literal(mir::Literal::Nil),
      hir::Expr::Literal(hir::Literal::Bool(v)) => mir::Expr::Literal(mir::Literal::Bool(v)),
      hir::Expr::Literal(hir::Literal::Int(v)) => mir::Expr::Literal(mir::Literal::Int(v)),

      // TODO: It'd be nice to remove StringInterp from MIR
      hir::Expr::String(ref segments) => {
        let segments = segments
          .iter()
          .map(|segment| match segment {
            hir::StringInterp::Literal(ref v) => mir::StringInterp::Literal(v.clone()),
            hir::StringInterp::Expr(e) => mir::StringInterp::Expr(self.lower_expr(*e)),
          })
          .collect();

        mir::Expr::StringInterp(segments)
      }

      hir::Expr::Array(ref exprs) => {
        let exprs = exprs.iter().map(|expr| self.lower_expr(*expr)).collect();

        let ty = match self.ty.type_of_expr(expr) {
          Type::Array(ty) => *ty,
          _ => unreachable!(),
        };

        mir::Expr::Array(exprs, ty)
      }

      // HIR should have fully qualified names, and the typer should get the type of this name.
      // We should probably convert it to something more useful than a string though.
      hir::Expr::Name(ref v) => match self.locals.get(v) {
        Some(local) => mir::Expr::Local(*local, self.ty.type_of_expr(expr)),
        None => match self.env.items[v] {
          Item::UserFunction(ref func) => {
            self.mir.deps.insert(func.id);
            mir::Expr::UserFunction(func.id, self.ty.type_of_expr(expr))
          }
          Item::NativeFunction(id) => mir::Expr::Native(id, self.ty.type_of_expr(expr)),
        },
      },

      hir::Expr::Block(ref block) => {
        let mut stmts = vec![];

        // FIXME: Make a new scope here so that local variables are local to blocks.
        for stmt in block.iter() {
          if let Some(stmt) = self.lower_stmt(*stmt) {
            stmts.push(stmt);
          }
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
          hir::BinaryOp::Xor => mir::BinaryOp::Xor,
          hir::BinaryOp::ShiftLeft => mir::BinaryOp::ShiftLeft,
          hir::BinaryOp::ShiftRight => mir::BinaryOp::ShiftRight,
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

      hir::Expr::Index(lhs, rhs) => {
        let lhs = self.lower_expr(lhs);
        let rhs = self.lower_expr(rhs);

        mir::Expr::Index(lhs, rhs, self.ty.type_of_expr(expr))
      }

      hir::Expr::Call(lhs, ref args) => match self.hir.exprs[lhs] {
        hir::Expr::Name(ref name) => {
          if let Some(Item::UserFunction(func)) = self.env.items.get(name) {
            self.mir.deps.insert(func.id);

            let lhs_ty = self.ty.type_of_expr(lhs);
            let args = args.iter().map(|&arg| self.lower_expr(arg)).collect();

            if let Some(intrinsic) = func.intrinsic {
              mir::Expr::CallIntrinsic(intrinsic, args)
            } else {
              mir::Expr::Call(func.id, lhs_ty, args)
            }
          } else {
            panic!("unresolved function {name}");
          }
        }
        _ => panic!("todo: dynamic dispatch"),
      },

      hir::Expr::If { cond, then, els } => {
        let cond = self.lower_expr(cond);
        let then = self.lower_expr(then);
        let els = els.map(|e| self.lower_expr(e));

        mir::Expr::If { cond, then, els, ty: self.ty.type_of_expr(expr) }
      }

      hir::Expr::StructInit(ref path, ref fields) => {
        let strct = self.env.ctx.struct_paths[path].clone();

        let fields =
          fields.iter().map(|(name, expr)| (name.clone(), self.lower_expr(*expr))).collect();

        mir::Expr::StructInit(strct, fields)
      }

      ref v => unimplemented!("lowering expression {v:?}"),
    };

    self.mir.exprs.alloc(expr)
  }
}
