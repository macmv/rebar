//! Lowers HIR and the result of typechecking into MIR.

use std::collections::HashMap;

use rb_diagnostic::emit;
use rb_hir::{
  FunctionSpanMap,
  ast::{self as hir, FullyQualifiedName, Path, Type},
};
use rb_mir::{
  MirContext, UserFunction,
  ast::{self as mir, FunctionId},
};
use rb_typer::Typer;

#[cfg(test)]
#[macro_use]
extern crate rb_test;

pub fn scan_module<'a>(
  module: &'a hir::Module,
  span_map: &'a rb_hir::SpanMap,
) -> (
  rb_mir::MirContext,
  HashMap<Path, rb_mir::ast::FunctionId>,
  Vec<(rb_mir::ast::FunctionId, &'a rb_hir::ast::Function, &'a rb_hir::FunctionSpanMap)>,
) {
  let mut mir_ctx = MirContext::default();
  let mut functions = vec![];
  let mut function_map = HashMap::new();
  let mut struct_id = rb_mir::ast::StructId(0);

  for (path, module) in module.modules() {
    let span_map = &span_map.modules[&path];
    for s in module.structs.values() {
      let struct_path = path.join(s.name.clone());

      mir_ctx.struct_paths.insert(struct_path, struct_id);
      mir_ctx.structs.insert(
        struct_id,
        rb_mir::Struct {
          fields: s
            .fields
            .iter()
            .map(|(name, te)| (name.clone(), rb_typer::type_of_type_expr(te)))
            .collect(),
        },
      );
      struct_id.0 += 1;
    }

    for (hir_id, f) in module.functions.iter() {
      let path = path.join(f.name.clone());
      let span_map = &span_map.functions[&hir_id];

      let mir_id = rb_mir::ast::FunctionId(functions.len() as u64);
      functions.push((mir_id, f, span_map));
      function_map.insert(path.clone(), mir_id);
      declare_user_function(&mut mir_ctx, mir_id, path.clone(), f, span_map);
    }
  }

  (mir_ctx, function_map, functions)
}

pub fn declare_user_function(
  ctx: &mut MirContext,
  id: FunctionId,
  path: Path,
  function: &hir::Function,
  span: &FunctionSpanMap,
) {
  let mut func = UserFunction { id, kind: rb_mir::FunctionKind::UserDefined };

  if let Some(ext) = &function.ext {
    if ext != "C" {
      emit!(span.name_span.unwrap() => "only extern 'C' functions are supported");
    }

    func.kind = rb_mir::FunctionKind::Extern(function.name.clone());
  }

  for attr in &function.attrs {
    if attr.path == "rebar::intrinsic" {
      let syscall = match function.name.as_str() {
        "syscall1" | "syscall2" | "syscall3" | "syscall4" | "syscall5" | "syscall6" => {
          mir::Intrinsic::Syscall
        }
        "slice_ptr" => mir::Intrinsic::SlicePtr,
        "slice_len" => mir::Intrinsic::SliceLen,
        "trap" => mir::Intrinsic::Trap,
        _ => {
          emit!(span.name_span.unwrap() => "unknown intrinsic {}", function.name);
          continue;
        }
      };

      func.kind = rb_mir::FunctionKind::Intrinsic(syscall);
    }
  }

  ctx.items.insert(FullyQualifiedName::new_bare(path).unwrap(), func);
}

pub fn lower_function(ctx: &MirContext, ty: &Typer, hir: &hir::Function) -> mir::Function {
  let mut mir = mir::Function::default();

  let mut lower = Lower { ctx, ty, hir, mir: &mut mir, locals: HashMap::new() };

  for (hir_id, local) in hir.locals.iter() {
    if let Some(ref ty) = local.ty {
      let ty = rb_typer::type_of_type_expr(ty);

      lower.mir.params.push(ty.clone());
      let id = lower.next_var_id(ty);
      lower.locals.insert(hir_id, id);
    }
  }

  lower.mir.ret = rb_typer::type_of_type_expr(&hir.sig.ret);

  if let Some(body) = &hir.body {
    for stmt in body.iter() {
      if let Some(stmt) = lower.lower_stmt(*stmt) {
        lower.mir.items.push(stmt);
      }
    }
  }

  mir
}

struct Lower<'a> {
  ctx: &'a MirContext,
  ty:  &'a Typer<'a>,
  hir: &'a hir::Function,
  mir: &'a mut mir::Function,

  locals: HashMap<hir::LocalId, mir::VarId>,
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
      hir::Stmt::Let(_, hir_id, _, expr) => {
        let mir_expr = self.lower_expr(expr);
        let ty = self.ty.type_of_expr(expr);
        let id = self.next_var_id(ty.clone());
        self.locals.insert(hir_id.unwrap(), id);
        mir::Stmt::Let(id, ty, mir_expr)
      }
      hir::Stmt::FunctionDef(_, _) | hir::Stmt::Struct => return None,
    };

    Some(self.mir.stmts.alloc(stmt))
  }

  fn lower_expr(&mut self, expr: hir::ExprId) -> mir::ExprId {
    let expr = match self.hir.exprs[expr] {
      hir::Expr::Literal(hir::Literal::Bool(v)) => mir::Expr::Literal(mir::Literal::Bool(v)),
      hir::Expr::Literal(hir::Literal::Int(v)) => mir::Expr::Literal(mir::Literal::Int(v)),

      hir::Expr::String(ref segments) => {
        if let &[hir::StringInterp::Literal(ref lit)] = segments.as_slice() {
          mir::Expr::Literal(mir::Literal::String(lit.clone()))
        } else {
          todo!("lowering interpolated strings literals")
        }
      }

      hir::Expr::Array(ref exprs) => {
        let exprs = exprs.iter().map(|expr| self.lower_expr(*expr)).collect();

        let ty = match self.ty.type_of_expr(expr) {
          Type::Array(ty) => *ty,
          _ => unreachable!(),
        };

        mir::Expr::Array(exprs, ty)
      }

      hir::Expr::Name(ref v) => {
        let func = &self.ctx.items[v];
        self.mir.deps.insert(func.id);
        mir::Expr::UserFunction(func.id, self.ty.type_of_expr(expr))
      }

      hir::Expr::Local(id) => mir::Expr::Local(self.locals[&id], self.ty.type_of_expr(expr)),

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

      hir::Expr::UnaryOp(inner, hir::UnaryOp::Ref) => {
        let inner = self.lower_expr(inner);

        mir::Expr::StoreStack(inner)
      }

      hir::Expr::UnaryOp(inner, ref op) => {
        let inner = self.lower_expr(inner);

        let op = match op {
          hir::UnaryOp::Not => mir::UnaryOp::Not,
          hir::UnaryOp::Neg => mir::UnaryOp::Neg,
          hir::UnaryOp::Deref => mir::UnaryOp::Deref,
          hir::UnaryOp::Ref => unreachable!(),
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

      // The typer has allowed it, so we can just lower the inner expression.
      //
      // TODO: Sign-extend when needed?
      hir::Expr::Cast(inner, _) => return self.lower_expr(inner),

      hir::Expr::Call(lhs, ref args) => match self.hir.exprs[lhs] {
        hir::Expr::Name(ref name) => {
          if let Some(func) = self.ctx.items.get(&name) {
            self.mir.deps.insert(func.id);

            let lhs_ty = self.ty.type_of_expr(lhs);
            let args = args.iter().map(|&arg| self.lower_expr(arg)).collect();

            match func.kind {
              rb_mir::FunctionKind::Intrinsic(i) => mir::Expr::CallIntrinsic(i, args),
              rb_mir::FunctionKind::UserDefined | rb_mir::FunctionKind::Extern(_) => {
                mir::Expr::Call(func.id, lhs_ty, args)
              }
            }
          } else {
            panic!("unresolved function {name}");
          }
        }
        ref e => panic!("todo: dispatch on {e:?}"),
      },

      hir::Expr::If { cond, then, els } => {
        let cond = self.lower_expr(cond);
        let then = self.lower_expr(then);
        let els = els.map(|e| self.lower_expr(e));

        mir::Expr::If { cond, then, els, ty: self.ty.type_of_expr(expr) }
      }

      hir::Expr::StructInit(ref path, ref fields) => {
        let strct = self.ctx.struct_paths[path];

        let fields =
          fields.iter().map(|(name, expr)| (name.clone(), self.lower_expr(*expr))).collect();

        mir::Expr::StructInit(strct, fields)
      }

      hir::Expr::Field(base, ref field) => {
        let base_ty = self.ty.type_of_expr(base);
        let base = self.lower_expr(base);

        match base_ty {
          Type::Ref(_, _) => {
            mir::Expr::PointerField(base, field.clone(), self.ty.type_of_expr(expr))
          }
          _ => mir::Expr::ValueField(base, field.clone(), self.ty.type_of_expr(expr)),
        }
      }

      ref v => unimplemented!("lowering expression {v:?}"),
    };

    self.mir.exprs.alloc(expr)
  }
}

#[cfg(test)]
fn check(body: &str, expected: rb_test::Expect) {
  use rb_hir::Environment;
  use std::fmt::Write;

  let mut env = Environment::mini();
  let (sources, module, module_span_map) = rb_hir_lower::parse_body(&env, body);
  rb_typer::scan_module(&module, &mut env);
  let mut span_map = rb_hir::SpanMap { modules: HashMap::from([(Path::new(), module_span_map)]) };
  let (mir_ctx, _, _) = scan_module(&module, &span_map);
  let mut module_span_map = span_map.modules.remove(&Path::new()).unwrap();

  let body = module.functions[module.main_function.unwrap()].clone();
  let span_map = module_span_map.functions.remove(&module.main_function.unwrap()).unwrap();

  let mut out = String::new();
  let res = rb_diagnostic::run(sources.clone(), || {
    let typer = crate::Typer::check(&env, &body, &span_map);
    if !rb_diagnostic::is_ok() {
      return;
    }

    let func = crate::lower_function(&mir_ctx, &typer, &body);

    write!(&mut out, "{}", func).unwrap();
  });

  match res {
    Ok(()) => expected.assert_eq(&format!("{out}")),
    Err(e) => {
      let mut out = String::new();
      for e in e {
        write!(out, "{}", e.render(&sources)).unwrap();
      }
      expected.assert_eq(&format!("{out}"));
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn numbers() {
    check(
      r#"
      let a: i32 = 3
      let b = a * 1 + 2
      "#,
      expect![@r#"
        function 0:
          let v1: i32 = 3;
          let v2: i32 = ((v1 * 1)::<i32> + 2)::<i32>;
      "#],
    );
  }

  #[test]
  fn struct_value() {
    check(
      r#"
      struct Foo {
        x: i64
        y: i64
      }

      let a = Foo { x: 10, y: 20 }
      let b = a.x
      "#,
      expect![@r#"
        function 0:
          let v0: Struct Foo = StructInit 0 { x: 10, y: 20 };
          let v1: i64 = v0.x::<i64>;
      "#],
    );
  }

  #[test]
  fn temporary_ref() {
    check(
      r#"
      fn foo(a: &u8) {}
      foo(&3)
      "#,
      expect![@r#"
        function 0:
          call 0::<fn(&u8) -> ()>(store_stack(3));
      "#],
    );
  }

  #[test]
  fn ref_fields() {
    check(
      r#"
      struct Foo {
        x: i64
      }

      let foo = &Foo { x: 3 }
      let a = foo.x
      "#,
      expect![@r#"
        function 0:
          let v0: &Struct Foo = store_stack(StructInit 0 { x: 3 });
          let v1: i64 = v0*.x::<i64>;
      "#],
    );
  }
}
