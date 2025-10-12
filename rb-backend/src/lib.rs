use codegen::{
  control::ControlPlane,
  ir::{self, FuncRef, Inst},
  CompiledCode,
};
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, FunctionDeclaration, Linkage, Module};
use isa::{CallConv, TargetFrontendConfig, TargetIsa};
use rb_mir::{
  ast::{self as mir, UserFunctionId},
  MirContext,
};
use rb_typer::{Literal, Type};
use slot::Slot;
use std::collections::HashMap;

mod r_value;
mod slot;

use r_value::RValue;

use rb_value::{DynamicValueType, IntrinsicImpls, ParamKind, ValueType};

pub struct Compiler {
  mir_ctx: MirContext,
  module:  JITModule,

  // TODO: Use this for string literals at the very least.
  #[allow(dead_code)]
  data_description: DataDescription,

  intrinsics: Intrinsics<FuncId>,
  user_funcs: HashMap<mir::UserFunctionId, (FuncId, Signature)>,
}

pub struct ThreadCtx<'a> {
  mir_ctx:         &'a MirContext,
  builder_context: FunctionBuilderContext,
  ctx:             codegen::Context,

  isa: &'a dyn TargetIsa,

  intrinsics: Intrinsics<IntrinsicDecl<'a>>,
  user_funcs: &'a HashMap<mir::UserFunctionId, (FuncId, Signature)>,
}

#[derive(Clone, Copy)]
struct IntrinsicDecl<'a> {
  id:   FuncId,
  decl: &'a FunctionDeclaration,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct IntrinsicId(u8);

macro_rules! intrinsics {
  ($(
    $id:literal: $name:ident($($arg:ident),*) $(-> $ret:ident)?,
  )*) => {
    pub struct Intrinsics<T> {
      $($name: T),*
    }

    mod intrinsic {
      use super::*;

      $(
        #[allow(non_upper_case_globals)]
        pub const $name: IntrinsicId = IntrinsicId($id);
      )*
    }

    impl<T: Copy> Intrinsics<T> {
      fn map<U>(&self, mut f: impl FnMut(T) -> U) -> Intrinsics<U> {
        Intrinsics {
          $($name: f(self.$name)),*
        }
      }
    }

    impl<T> Intrinsics<T> where T: Copy {
      pub fn all(v: T) -> Self {
        Intrinsics {
          $($name: v),*
        }
      }
    }

    impl<T> std::ops::Index<IntrinsicId> for Intrinsics<T> {
      type Output = T;

      fn index(&self, id: IntrinsicId) -> &T {
        match id {
          $(
            intrinsic::$name => &self.$name,
          )*
          _ => unreachable!(),
        }
      }
    }

    impl<T> std::ops::IndexMut<IntrinsicId> for Intrinsics<T> {
      fn index_mut(&mut self, id: IntrinsicId) -> &mut T {
        match id {
          $(
            intrinsic::$name => &mut self.$name,
          )*
          _ => unreachable!(),
        }
      }
    }

    impl Intrinsics<FuncId> {
      pub fn prepare(builder: &mut JITBuilder, impls: &IntrinsicImpls) {
        $(
          builder.symbol(concat!("__", stringify!($name)), impls.$name as *const _);
        )*
      }

      pub fn build(module: &mut JITModule) -> Self {
        Intrinsics {
          $(
            $name: module.declare_function(
              concat!("__", stringify!($name)),
              Linkage::Import,
              &{
                #[allow(unused_mut)]
                let mut sig = module.make_signature();
                $(
                  sig.params.push(AbiParam::new(ir::types::$arg));
                )*
                $(
                  sig.returns.push(AbiParam::new(ir::types::$ret));
                )?
                sig
              }
            ).unwrap()
          ),*
        }
      }
    }
  };
}

intrinsics!(
  0: call(I64, I64, I64),
  1: push_frame(),
  2: pop_frame(),
  3: gc_collect(),
  4: track(I64),
  5: string_append_value(I64, I64),
  6: string_append_str(I64, I64, I64),
  7: string_new() -> I64,
  8: array_new(I64, I64) -> I64,
  9: value_equals(I64, I64) -> I8,
);

pub struct FuncBuilder<'a> {
  ctx:            &'a MirContext,
  isa:            &'a dyn TargetIsa,
  intrinsic_defs: &'a Intrinsics<IntrinsicDecl<'a>>,

  builder:    FunctionBuilder<'a>,
  mir:        &'a mir::Function,
  intrinsics: Intrinsics<Option<FuncRef>>,

  // Note that `VarId` and `Variable` are entirely distinct.
  //
  // `VarId` is an opaque identifier for a local variable in the AST, whereas `Variable` is a
  // cranelift IR variable. There will usually be more cranelift variables than local variables.
  locals:        HashMap<mir::VarId, Slot<Variable>>,
  next_variable: usize,

  // A map of user-defined function calls to function refs.
  user_funcs: HashMap<mir::UserFunctionId, FuncRef>,
}

const DEBUG: bool = false;

impl Compiler {
  #[allow(clippy::new_without_default)]
  pub fn new(mir_ctx: MirContext, intrinsics: IntrinsicImpls) -> Self {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    flag_builder.set("opt_level", "speed_and_size").unwrap();
    let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
      panic!("host machine is not supported: {}", msg);
    });
    let isa = isa_builder.finish(settings::Flags::new(flag_builder)).unwrap();
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

    Intrinsics::prepare(&mut builder, &intrinsics);

    let mut module = JITModule::new(builder);

    Compiler {
      mir_ctx,
      data_description: DataDescription::new(),
      intrinsics: Intrinsics::build(&mut module),
      module,
      user_funcs: HashMap::new(),
    }
  }

  pub fn new_thread(&self) -> ThreadCtx<'_> {
    let ctx = self.module.make_context();

    ThreadCtx {
      mir_ctx: &self.mir_ctx,
      builder_context: FunctionBuilderContext::new(),
      ctx,
      isa: self.module.isa(),

      intrinsics: self.intrinsics(),
      user_funcs: &self.user_funcs,
    }
  }

  fn intrinsics(&self) -> Intrinsics<IntrinsicDecl<'_>> {
    self
      .intrinsics
      .map(|id| IntrinsicDecl { id, decl: self.module.declarations().get_function_decl(id) })
  }

  pub fn finalize(&mut self) { self.module.finalize_definitions().unwrap(); }

  pub fn eval(&mut self, id: FuncId) {
    let code = self.module.get_finalized_function(id);

    unsafe {
      let code: fn() = std::mem::transmute(code);
      code();
    }
  }
}

impl ThreadCtx<'_> {
  pub fn new_function<'a>(&'a mut self, mir: &'a mir::Function) -> FuncBuilder<'a> {
    let builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

    let mut user_funcs = HashMap::new();
    for &dep in mir.deps.iter() {
      let (id, signature) = &self.user_funcs[&dep];

      let signature = builder.func.import_signature(signature.clone());
      let user_name_ref = builder.func.declare_imported_user_function(ir::UserExternalName {
        namespace: 0,
        index:     id.as_u32(),
      });
      let func_ref = builder.func.import_function(ir::ExtFuncData {
        name: ir::ExternalName::user(user_name_ref),
        signature,
        colocated: false,
      });
      user_funcs.insert(dep, func_ref);
    }

    FuncBuilder {
      ctx: self.mir_ctx,
      isa: self.isa,
      intrinsic_defs: &self.intrinsics,
      builder,
      mir,
      intrinsics: Intrinsics::all(None),
      locals: HashMap::new(),
      next_variable: 0,
      user_funcs,
    }
  }

  fn translate_function(&mut self, mir: &mir::Function) { self.new_function(mir).translate(); }

  fn compile(&mut self) -> &CompiledCode {
    if DEBUG {
      self.ctx.want_disasm = true;
    }

    let code = self.ctx.compile(self.isa, &mut ControlPlane::default()).unwrap();

    if DEBUG {
      println!("debug asm:");
      println!("{}", code.vcode.as_ref().unwrap());
    }

    code
  }

  fn clear(&mut self) { self.ctx.clear(); }

  pub fn compile_function(&mut self, mir: &mir::Function) -> CompiledFunction {
    let (id, sig) = &self.user_funcs[&mir.id];
    self.ctx.func = ir::Function::with_name_signature(
      ir::UserFuncName::User(ir::UserExternalName { namespace: 0, index: id.as_u32() }),
      sig.clone(),
    );

    self.translate_function(mir);
    let code = self.compile().clone();

    let compiled = CompiledFunction { id: mir.id, code, func: self.ctx.func.clone() };

    self.clear();

    compiled
  }
}

pub struct CompiledFunction {
  id:   UserFunctionId,
  code: CompiledCode,
  func: ir::Function,
}

impl FuncBuilder<'_> {
  fn target_frontend_config(&self) -> TargetFrontendConfig {
    TargetFrontendConfig {
      default_call_conv: self.isa.default_call_conv(),
      pointer_width:     self.isa.triple().pointer_width().unwrap(),
    }
  }

  fn call_intrinsic(&mut self, intrinsic: IntrinsicId, args: &[ir::Value]) -> Inst {
    let intrinsic_ref = &mut self.intrinsics[intrinsic];

    if intrinsic_ref.is_none() {
      let def = self.intrinsic_defs[intrinsic];

      let signature = self.builder.func.import_signature(def.decl.signature.clone());
      let user_name_ref = self.builder.func.declare_imported_user_function(ir::UserExternalName {
        namespace: 0,
        index:     def.id.as_u32(),
      });
      let colocated = def.decl.linkage.is_final();
      let func = self.builder.func.import_function(ir::ExtFuncData {
        name: ir::ExternalName::user(user_name_ref),
        signature,
        colocated,
      });

      *intrinsic_ref = Some(func);
    }

    self.builder.ins().call(intrinsic_ref.unwrap(), args)
  }

  fn translate(mut self) {
    let entry_block = self.builder.create_block();

    let mut param_values = vec![];

    for ty in self.mir.params.iter() {
      let vt = DynamicValueType::for_type(self.ctx, ty);

      let mut values = vec![];
      for _ in 0..vt.len(self.ctx) {
        let value = self.builder.append_block_param(entry_block, ir::types::I64);
        values.push(value);
      }

      param_values.push(values);
    }

    if let Some(ref ty) = self.mir.ret {
      match DynamicValueType::for_type(self.ctx, ty) {
        DynamicValueType::Union(_) => todo!("Extended variables not supported for parameters yet"),
        _ => {}
      }

      assert!(self.builder.func.signature.returns.len() == 1);
    } else {
      assert!(self.builder.func.signature.returns.is_empty());
    }

    self.builder.switch_to_block(entry_block);
    self.builder.seal_block(entry_block);

    self.call_intrinsic(intrinsic::push_frame, &[]);

    for (id, values) in param_values.into_iter().enumerate() {
      let len = values.len();
      let slot = Slot::<Variable>::new(&mut self, len);

      self.locals.insert(mir::VarId(id as u32), slot.clone());
      slot.copy_from_slice(&mut self.builder, &values);
    }

    for &stmt in &self.mir.items {
      let _res = self.compile_stmt(stmt);
      // self.def_var(return_variable, res.to_ir());
    }

    self.call_intrinsic(intrinsic::pop_frame, &[]);

    // Emit the return instruction.
    self.builder.ins().return_(&[]);

    if DEBUG {
      println!("done translating {:?}. cranelift ir:", self.mir.id);
      println!("{}", self.builder.func);
    }

    // Tell the builder we're done with this function.
    self.builder.finalize();
  }
}

impl Compiler {
  pub fn declare_function(&mut self, func: &mir::Function) {
    let mut sig = self.module.make_signature();

    sig.call_conv = CallConv::Fast;
    for ty in func.params.iter() {
      let dvt = DynamicValueType::for_type(&self.mir_ctx, ty);
      for _ in 0..dvt.len(&self.mir_ctx) {
        sig.params.push(AbiParam::new(ir::types::I64));
      }
    }

    let id = self
      .module
      .declare_function(&format!("fooooooo_{}", func.id.0), Linkage::Local, &sig)
      .unwrap();
    self.user_funcs.insert(func.id, (id, sig));
  }

  pub fn define_function(&mut self, func: CompiledFunction) -> Result<FuncId, String> {
    let (id, _) = self.user_funcs[&func.id];

    self
      .module
      .define_function_bytes(
        id,
        &func.func,
        u64::from(func.code.buffer.alignment),
        func.code.code_buffer(),
        func.code.buffer.relocs(),
      )
      .map_err(|e| e.to_string())?;
    Ok(id)
  }
}

#[derive(Debug)]
pub enum Error {
  MissingExpr,
}

impl FuncBuilder<'_> {
  fn compile_stmt(&mut self, stmt: mir::StmtId) -> RValue {
    match self.mir.stmts[stmt] {
      mir::Stmt::Expr(expr) => self.compile_expr(expr),
      mir::Stmt::Let(id, ref ty, expr) => {
        let value = self.compile_expr(expr);
        let ir = value.to_ir(DynamicValueType::for_type(self.ctx, &ty).param_kind(self.ctx), self);

        let slot = Slot::<Variable>::new(self, ir.len());

        slot.copy_from(&mut self.builder, &ir);
        self.locals.insert(id, slot);

        if self.type_needs_gc(ty) {
          let arg_ptr = self.stack_slot_unsized(&value);

          self.call_intrinsic(intrinsic::track, &[arg_ptr]);
        }

        self.call_intrinsic(intrinsic::gc_collect, &[]);

        RValue::nil()
      }
    }
  }

  fn type_needs_gc(&self, ty: &Type) -> bool {
    match ty {
      Type::Literal(Literal::Unit) => false,
      Type::Literal(Literal::Int) => false,
      Type::Literal(Literal::Bool) => false,
      Type::Literal(Literal::String) => true,
      Type::Array(_) => true,
      Type::Union(vs) => vs.iter().any(|v| self.type_needs_gc(v)),

      // TODO: uhhhhhhhhhh
      Type::Function(..) => false,

      Type::Struct(id) => {
        let id = self.ctx.struct_paths[id];
        self.ctx.structs[&id].fields.iter().any(|(_, ty)| self.type_needs_gc(ty))
      }
    }
  }

  fn compile_expr(&mut self, expr: mir::ExprId) -> RValue {
    match self.mir.exprs[expr] {
      mir::Expr::Literal(ref lit) => match lit {
        mir::Literal::Nil => RValue::nil(),
        mir::Literal::Bool(v) => RValue::bool(self.builder.ins().iconst(ir::types::I8, *v as i64)),
        mir::Literal::Int(i) => RValue::int(self.builder.ins().iconst(ir::types::I64, *i)),
        mir::Literal::String(i) => {
          let str = self.call_intrinsic(intrinsic::string_new, &[]);
          let str = self.builder.inst_results(str)[0];

          let mut to_leak = i.clone();
          to_leak.shrink_to_fit();

          let len = to_leak.len();
          let ptr = to_leak.as_ptr();

          let ptr = self.builder.ins().iconst(ir::types::I64, ptr as i64);
          let len = self.builder.ins().iconst(ir::types::I64, len as i64);

          // TODO: Throw this in a GC or something.
          String::leak(to_leak);

          self.call_intrinsic(intrinsic::string_append_str, &[str, ptr, len]);

          RValue::TypedDyn(ValueType::String, Slot::Single(str))
        }
      },

      mir::Expr::StringInterp(ref segments) => {
        // This is a bit of nonsense, but here we go:
        //
        // - First, we make a new string to work with.
        // - Second, we start appending things:
        //   - String literals are easy, those get baked into the binary and appended
        //     directly.
        //   - Expressions get compiled in inline. The result of the expression is then
        //     sent to a native function to stringify it, which will append to our
        //     string in the heap.
        // - Once we're done, we can throw the resulting string onto the heap, now that
        //   we're done mutating it.

        // We track this in the GC later, once we're done mutating it. For now, manually
        // drop it so we don't double free.
        let ret = self.call_intrinsic(intrinsic::string_new, &[]);
        let str = self.builder.inst_results(ret)[0];

        for segment in segments {
          match segment {
            mir::StringInterp::Literal(s) => {
              let mut v = String::from(s);
              v.shrink_to_fit();

              let len = v.len();
              let ptr = v.as_ptr();

              let ptr = self.builder.ins().iconst(ir::types::I64, ptr as i64);
              let len = self.builder.ins().iconst(ir::types::I64, len as i64);

              // TODO: Keep this in a memoized string table.
              String::leak(v);

              self.call_intrinsic(intrinsic::string_append_str, &[str, ptr, len]);
            }

            mir::StringInterp::Expr(e) => {
              let value = self.compile_expr(*e);
              let arg_ptr = self.stack_slot_unsized(&value);

              self.call_intrinsic(intrinsic::string_append_value, &[str, arg_ptr]);
            }
          };
        }

        RValue::TypedDyn(ValueType::String, Slot::Single(str))
      }

      mir::Expr::Array(ref exprs, ref ty) => {
        let vt = DynamicValueType::for_type(self.ctx, ty);
        let slot_size = vt.len(self.ctx);

        let result_ptr = {
          let vt = self.builder.ins().iconst(ir::types::I64, vt.encode());
          let len = self.builder.ins().iconst(ir::types::I64, exprs.len() as i64);

          let result_ptr = self.call_intrinsic(intrinsic::array_new, &[len, vt]);
          self.builder.inst_results(result_ptr)[0]
        };

        // `result_ptr` points to an `RbArray`, which has the elements pointer as the
        // first element. So pick that pointer out, and use that when filling in
        // elements.
        let first_ptr = self.builder.ins().load(ir::types::I64, MemFlags::new(), result_ptr, 0);

        for (i, expr) in exprs.iter().enumerate() {
          let to_append = self.compile_expr(*expr);
          let ir = to_append.to_ir(vt.param_kind(self.ctx), self);
          assert_eq!(ir.len(), slot_size as usize);

          let offset = self.builder.ins().iconst(ir::types::I64, i as i64 * slot_size as i64 * 8);
          let element_ptr = self.builder.ins().iadd(first_ptr, offset);

          ir.copy_to(self, element_ptr);
        }

        RValue::TypedDyn(ValueType::Array, Slot::Single(result_ptr))
      }

      mir::Expr::Local(id, ref ty) => {
        let var = &self.locals[&id];

        let dvt = DynamicValueType::for_type(self.ctx, ty);
        assert_eq!(var.len() as u32, dvt.len(self.ctx), "variable length mismatch for type {ty:?}");

        match dvt {
          DynamicValueType::Const(ty) => RValue::TypedDyn(
            ty,
            match var {
              Slot::Empty => Slot::Empty,
              Slot::Single(v) => Slot::Single(self.builder.use_var(*v)),
              Slot::Multiple(len, slot) => Slot::Multiple(*len, slot.clone()),
            },
          ),

          DynamicValueType::Union(_) => RValue::Untyped(match var {
            Slot::Empty => Slot::Empty,
            Slot::Single(v) => Slot::Single(self.builder.use_var(*v)),
            Slot::Multiple(len, slot) => Slot::Multiple(*len, slot.clone()),
          }),
        }
      }

      mir::Expr::UserFunction(id, _) => {
        RValue::TypedConst(ValueType::UserFunction, vec![id.0 as i64])
      }

      mir::Expr::Native(ref id, _) => {
        RValue::function(self.builder.ins().iconst(ir::types::I64, id.0 as i64))
      }

      mir::Expr::Block(ref stmts) => {
        // FIXME: Make a new scope so that locals don't leak.
        let mut return_value = RValue::nil();
        self.call_intrinsic(intrinsic::push_frame, &[]);

        for &stmt in stmts {
          return_value = self.compile_stmt(stmt);
        }

        self.call_intrinsic(intrinsic::pop_frame, &[]);
        return_value
      }

      mir::Expr::Call(lhs, ref sig_ty, ref args) => {
        let lhs = self.compile_expr(lhs);

        match lhs.const_ty() {
          Some(ValueType::Function) => {
            let arg_types = match sig_ty {
              Type::Function(ref args, _) => args,
              _ => unreachable!(),
            };

            // Argument length in 8 byte increments.
            let mut arg_values = vec![];
            for (&arg, arg_ty) in args.iter().zip(arg_types.iter()) {
              let arg = self.compile_expr(arg);

              let v =
                arg.to_ir(DynamicValueType::for_type(self.ctx, &arg_ty).param_kind(self.ctx), self);
              arg_values.push(v);
            }

            let native = lhs.unwrap_single(self);

            let ret_ty = match *sig_ty {
              Type::Function(_, ref ret) => ret,
              _ => unreachable!(),
            };

            self.call_native(native, &arg_values, arg_types, &**ret_ty)
          }

          Some(ValueType::UserFunction) => {
            let id = match lhs {
              RValue::TypedConst(_, v) => UserFunctionId(v[0] as u64),
              _ => todo!(),
            };

            let arg_types = match sig_ty {
              Type::Function(ref args, _) => args,
              _ => unreachable!(),
            };

            assert_eq!(args.len(), arg_types.len());

            // Argument length in 8 byte increments.
            let mut arg_values = vec![];
            for (&arg, arg_ty) in args.iter().zip(arg_types.iter()) {
              let arg = self.compile_expr(arg);

              let slot =
                arg.to_ir(DynamicValueType::for_type(self.ctx, &arg_ty).param_kind(self.ctx), self);
              match slot {
                Slot::Empty => {}
                Slot::Single(v) => {
                  use cranelift::codegen::ir::InstBuilderBase;

                  match self.builder.ins().data_flow_graph_mut().value_type(v) {
                    ir::types::I64 => arg_values.push(v),
                    _ => {
                      let v2 = self.builder.ins().uextend(ir::types::I64, v);
                      arg_values.push(v2);
                    }
                  }
                }
                Slot::Multiple(len, slot) => {
                  for i in 0..len {
                    arg_values.push(self.builder.ins().stack_load(
                      ir::types::I64,
                      slot.clone(),
                      i as i32 * 8,
                    ));
                  }
                }
              }
            }

            let func_ref = self.user_funcs[&id];
            let call = self.builder.ins().call(func_ref, &arg_values);

            match *sig_ty {
              Type::Function(_, ref ret) => match **ret {
                // FIXME: Need to create RValues from ir extended form.
                Type::Literal(Literal::Unit) => RValue::nil(),
                _ => RValue::int(self.builder.inst_results(call)[0]),
              },
              _ => unreachable!(),
            }
          }

          _ => unreachable!(),
        }
      }

      mir::Expr::Unary(lhs, ref op, _) => {
        let lhs = self.compile_expr(lhs);
        let lhs = lhs.unwrap_single(self);

        let res = match op {
          mir::UnaryOp::Neg => RValue::int(self.builder.ins().ineg(lhs)),
          mir::UnaryOp::Not => RValue::bool(self.builder.ins().bxor_imm(lhs, 1)),
        };

        res
      }

      mir::Expr::Binary(lhs, ref op, rhs, _) => {
        let lhs = self.compile_expr(lhs);
        let rhs = self.compile_expr(rhs);

        let res = match op {
          mir::BinaryOp::Add
          | mir::BinaryOp::Sub
          | mir::BinaryOp::Mul
          | mir::BinaryOp::Div
          | mir::BinaryOp::Mod => {
            let lhs = lhs.unwrap_single(self);
            let rhs = rhs.unwrap_single(self);

            let res = match op {
              mir::BinaryOp::Add => self.builder.ins().iadd(lhs, rhs),
              mir::BinaryOp::Sub => self.builder.ins().isub(lhs, rhs),
              mir::BinaryOp::Mul => self.builder.ins().imul(lhs, rhs),
              mir::BinaryOp::Div => self.builder.ins().udiv(lhs, rhs),
              mir::BinaryOp::Mod => self.builder.ins().urem(lhs, rhs),
              _ => unreachable!(),
            };

            RValue::int(res)
          }

          mir::BinaryOp::Eq | mir::BinaryOp::Neq => match (lhs.const_ty(), rhs.const_ty()) {
            (Some(ValueType::Nil), Some(ValueType::Nil)) => {
              let tru = self.builder.ins().iconst(ir::types::I8, 1);
              RValue::bool(tru)
            }
            (Some(ValueType::Bool), Some(ValueType::Bool)) => {
              let l = lhs.unwrap_single(self);
              let r = rhs.unwrap_single(self);

              let res = match op {
                mir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, l, r),
                mir::BinaryOp::Neq => self.builder.ins().icmp(IntCC::NotEqual, l, r),
                _ => unreachable!(),
              };

              RValue::bool(res)
            }
            (Some(ValueType::Int), Some(ValueType::Int)) => {
              let l = lhs.unwrap_single(self);
              let r = rhs.unwrap_single(self);

              let res = match op {
                mir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, l, r),
                mir::BinaryOp::Neq => self.builder.ins().icmp(IntCC::NotEqual, l, r),
                _ => unreachable!(),
              };

              RValue::bool(res)
            }

            (Some(a), Some(b)) if a != b => RValue::const_bool(false),

            // TODO: Theres a couple more branches we could optimize for here, but the dynamic path
            // is nice to fall back on.
            (_, _) => {
              let l_addr = self.stack_slot_unsized(&lhs);
              let r_addr = self.stack_slot_unsized(&rhs);

              let ret = self.call_intrinsic(intrinsic::value_equals, &[l_addr, r_addr]);

              RValue::bool(self.builder.inst_results(ret)[0])
            }
          },

          _ => {
            let lhs = lhs.unwrap_single(self);
            let rhs = rhs.unwrap_single(self);

            // All numbers are signed.
            let res = match op {
              mir::BinaryOp::Lt => self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs),
              mir::BinaryOp::Lte => self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, lhs, rhs),
              mir::BinaryOp::Gt => self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs),
              mir::BinaryOp::Gte => {
                self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs)
              }

              _ => unreachable!(),
            };

            RValue::bool(res)
          }
        };

        res
      }

      mir::Expr::Index(lhs, rhs, ref ret_ty) => {
        let lhs = self.compile_expr(lhs);
        let rhs = self.compile_expr(rhs);

        let ret_dvt = DynamicValueType::for_type(self.ctx, ret_ty);

        // `lhs` must be an array. Arrays are represented as a `Box<RbArray>`. `RbArray`
        // stores the pointer to its elements at the start, so we can simply read at the
        // pointer `lhs` to get the pointer to the first element. Then, we offset that
        // pointer by the integer `rhs` times the slot_size (which can be found by
        // looking at `ret_ty`).

        let array_ptr = lhs.unwrap_single(self);

        let first_ptr = self.builder.ins().load(ir::types::I64, MemFlags::new(), array_ptr, 0);

        let slot_size = ret_dvt.len(self.ctx);
        let slot_size = self.builder.ins().iconst(ir::types::I64, slot_size as i64 * 8);

        let index = rhs.unwrap_single(self);

        let offset = self.builder.ins().imul(index, slot_size);
        let element_ptr = self.builder.ins().iadd(first_ptr, offset);

        match ret_dvt {
          DynamicValueType::Const(vt) => RValue::TypedPtr(vt, element_ptr),
          DynamicValueType::Union(len) => RValue::UntypedPtr(len, element_ptr),
        }
      }

      mir::Expr::If { cond, then, els: None, ty: _ } => {
        let cond = self.compile_expr(cond);
        let cond = cond.unwrap_single(self);

        let then_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Test the if condition and conditionally branch.
        self.builder.ins().brif(cond, then_block, &[], merge_block, &[]);

        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        self.compile_expr(then);

        self.builder.ins().jump(merge_block, &[]);

        // Use `merge_block` for the rest of the function.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        RValue::nil()
      }

      mir::Expr::If { cond, then, els: Some(els), ref ty } => {
        let cond = self.compile_expr(cond);
        let cond = cond.unwrap_single(self);

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        let dvt = DynamicValueType::for_type(self.ctx, &ty);
        let param_kind = dvt.param_kind(self.ctx);

        if dvt.len(self.ctx) == 0 {
          // Test the if condition and conditionally branch.
          self.builder.ins().brif(cond, then_block, &[], else_block, &[]);

          self.builder.switch_to_block(then_block);
          self.builder.seal_block(then_block);
          self.compile_expr(then).to_ir(param_kind, self);

          self.builder.ins().jump(merge_block, &[]);

          self.builder.switch_to_block(else_block);
          self.builder.seal_block(else_block);
          self.compile_expr(els).to_ir(param_kind, self);

          self.builder.ins().jump(merge_block, &[]);

          self.builder.switch_to_block(merge_block);
          self.builder.seal_block(merge_block);

          RValue::nil()
        } else if dvt.len(self.ctx) == 1 {
          // Special case: if `dvt.len() == 1`, we can avoid creating a stack slot, and
          // just use a block parameter.
          self.builder.append_block_param(merge_block, cranelift::codegen::ir::types::I64);

          // Test the if condition and conditionally branch.
          self.builder.ins().brif(cond, then_block, &[], else_block, &[]);

          self.builder.switch_to_block(then_block);
          self.builder.seal_block(then_block);
          let then_return = self.compile_expr(then).to_ir(param_kind, self);

          self.builder.ins().jump(
            merge_block,
            &[match then_return {
              Slot::Single(v) => v,
              _ => unreachable!("cannot produce multiple values for a block with only 1 argument"),
            }],
          );

          self.builder.switch_to_block(else_block);
          self.builder.seal_block(else_block);
          let else_return = self.compile_expr(els).to_ir(param_kind, self);

          self.builder.ins().jump(
            merge_block,
            &[match else_return {
              Slot::Single(v) => v,
              _ => unreachable!("cannot produce multiple values for a block with only 1 argument"),
            }],
          );

          self.builder.switch_to_block(merge_block);
          self.builder.seal_block(merge_block);

          match dvt {
            DynamicValueType::Const(vt) => {
              RValue::TypedDyn(vt, Slot::Single(self.builder.block_params(merge_block)[0]))
            }
            DynamicValueType::Union(_) => {
              RValue::Untyped(Slot::Single(self.builder.block_params(merge_block)[0]))
            }
          }
        } else {
          let slot = self.builder.create_sized_stack_slot(StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: dvt.len(self.ctx) as u32 * 8,
          });
          let addr = self.builder.ins().stack_addr(ir::types::I64, slot.clone(), 0);

          // Test the if condition and conditionally branch.
          self.builder.ins().brif(cond, then_block, &[], else_block, &[]);

          self.builder.switch_to_block(then_block);
          self.builder.seal_block(then_block);
          let then_return = self.compile_expr(then).to_ir(param_kind, self);
          then_return.copy_to(self, addr);

          self.builder.ins().jump(merge_block, &[]);

          self.builder.switch_to_block(else_block);
          self.builder.seal_block(else_block);
          let else_return = self.compile_expr(els).to_ir(param_kind, self);
          else_return.copy_to(self, addr);

          self.builder.ins().jump(merge_block, &[]);

          self.builder.switch_to_block(merge_block);
          self.builder.seal_block(merge_block);

          match dvt {
            DynamicValueType::Const(vt) => {
              RValue::TypedDyn(vt, Slot::Multiple(dvt.len(self.ctx) as usize, slot))
            }
            DynamicValueType::Union(_) => {
              RValue::Untyped(Slot::Multiple(dvt.len(self.ctx) as usize, slot))
            }
          }
        }
      }

      mir::Expr::StructInit(id, ref fields) => {
        let strct = self.ctx.structs.get(&id).unwrap();
        let len = strct
          .fields
          .iter()
          .map(|(_, ty)| DynamicValueType::for_type(self.ctx, ty).len(self.ctx) as u32)
          .sum();
        let slot = self
          .builder
          .create_sized_stack_slot(StackSlotData { kind: StackSlotKind::ExplicitSlot, size: len });

        // Insert instructions in order of `fields`, but fill in `values` in order of
        // `strct.fields`.
        for (field, expr) in fields.iter() {
          let value = self.compile_expr(*expr);
          let ir = value.to_ir(
            DynamicValueType::for_type(
              self.ctx,
              &strct.fields.iter().find(|(n, _)| n == field).unwrap().1,
            )
            .param_kind(self.ctx),
            self,
          );

          let offset = strct
            .fields
            .iter()
            .try_fold(0, |o, f| {
              if f.0 == *field {
                Err(o)
              } else {
                Ok(o + DynamicValueType::for_type(self.ctx, &f.1).len(self.ctx))
              }
            })
            .unwrap_err() as usize;

          let addr = self.builder.ins().stack_addr(ir::types::I64, slot.clone(), offset as i32 * 8);
          ir.copy_to(self, addr);
        }

        RValue::TypedDyn(ValueType::Struct(id), Slot::Multiple(len as usize, slot))
      }

      ref v => unimplemented!("expr: {v:?}"),
    }
  }

  fn call_native(
    &mut self,
    native: ir::Value,
    args: &[Slot],
    arg_types: &[Type],
    ret_ty: &Type,
  ) -> RValue {
    assert_eq!(args.len(), arg_types.len());

    let ret_dvt = DynamicValueType::for_type(self.ctx, ret_ty);

    let arg_len = args.iter().map(|v| v.len()).sum::<usize>();

    let arg_slot = self.builder.create_sized_stack_slot(StackSlotData {
      kind: StackSlotKind::ExplicitSlot,
      // Each argument is 8 bytes wide.
      size: arg_len as u32 * 8,
    });
    let ret_slot = self.builder.create_sized_stack_slot(StackSlotData {
      kind: StackSlotKind::ExplicitSlot,
      // Each return value is 8 bytes wide.
      size: ret_dvt.len(self.ctx) * 8,
    });

    let mut slot_index = 0;
    for ir in args {
      let addr = self.builder.ins().stack_addr(ir::types::I64, arg_slot, slot_index as i32 * 8);
      ir.copy_to(self, addr);
      slot_index += ir.len();
    }

    let arg_ptr = self.builder.ins().stack_addr(ir::types::I64, arg_slot, 0);
    let ret_ptr = self.builder.ins().stack_addr(ir::types::I64, ret_slot, 0);

    self.call_intrinsic(intrinsic::call, &[native, arg_ptr, ret_ptr]);

    match ret_dvt {
      DynamicValueType::Const(vt) => {
        RValue::TypedDyn(vt, Slot::Multiple(ret_dvt.len(self.ctx) as usize, ret_slot))
      }
      DynamicValueType::Union(_) => {
        RValue::Untyped(Slot::Multiple(ret_dvt.len(self.ctx) as usize, ret_slot))
      }
    }
  }

  /// Creates a stack slot that stores a single unsized value, and returns the
  /// address to that slot. Used when calling native functions.
  fn stack_slot_unsized(&mut self, value: &RValue) -> ir::Value {
    let ir = value.to_ir(ParamKind::Unsized, self);

    match ir {
      Slot::Empty => {
        let dangling: *const i64 = std::ptr::dangling();
        self.builder.ins().iconst(ir::types::I64, dangling as i64)
      }
      Slot::Single(v) => {
        let slot = self
          .builder
          .create_sized_stack_slot(StackSlotData { kind: StackSlotKind::ExplicitSlot, size: 8 });

        self.builder.ins().stack_store(v, slot, 0);
        self.builder.ins().stack_addr(ir::types::I64, slot, 0)
      }
      Slot::Multiple(_, slot) => self.builder.ins().stack_addr(ir::types::I64, slot, 0),
    }
  }
}
