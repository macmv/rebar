use codegen::{
  control::ControlPlane,
  ir::{self, FuncRef},
  CompiledCode,
};
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, FunctionDeclaration, Linkage, Module};
use isa::{CallConv, TargetIsa};
use rb_mir::ast::{self as mir, UserFunctionId};
use rb_typer::{Literal, Type};
use std::{collections::HashMap, marker::PhantomPinned};

use crate::value::{CompactValues, ParamKind, RValue, Value, ValueType};

pub struct JIT {
  module: JITModule,

  // TODO: Use this for string literals at the very least.
  #[allow(dead_code)]
  data_description: DataDescription,

  funcs:      NativeFuncs<FuncId>,
  user_funcs: HashMap<mir::UserFunctionId, (FuncId, Signature)>,
}

pub struct ThreadCtx<'a> {
  builder_context: FunctionBuilderContext,
  ctx:             codegen::Context,

  isa: &'a dyn TargetIsa,

  funcs:      NativeFuncs<NativeFuncDecl<'a>>,
  user_funcs: &'a HashMap<mir::UserFunctionId, (FuncId, Signature)>,
}

#[derive(Clone, Copy)]
struct NativeFuncDecl<'a> {
  id:   FuncId,
  decl: &'a FunctionDeclaration,
}

struct NativeFuncs<T> {
  call:       T,
  push_frame: T,
  pop_frame:  T,
}

impl<T: Copy> NativeFuncs<T> {
  fn map<U>(&self, mut f: impl FnMut(T) -> U) -> NativeFuncs<U> {
    NativeFuncs {
      call:       f(self.call),
      push_frame: f(self.push_frame),
      pop_frame:  f(self.pop_frame),
    }
  }
}

pub struct FuncBuilder<'a> {
  builder: FunctionBuilder<'a>,
  mir:     &'a mir::Function,
  funcs:   NativeFuncs<FuncRef>,

  // Note that `VarId` and `Variable` are entirely distinct.
  //
  // `VarId` is an opaque identifier for a local variable in the AST, whereas `Variable` is a
  // cranelift IR variable. There will usually be more cranelift variables than local variables.
  locals:        HashMap<mir::VarId, Vec<Variable>>,
  next_variable: usize,

  // A map of user-defined function calls to function refs.
  user_funcs: HashMap<mir::UserFunctionId, FuncRef>,
}

/// This struct is horribly dangerous to use. It is a struct storing the
/// arguments passed from the Rebar runtime up to rust code. Because calls know
/// the signature of the called function statically, this struct's layout
/// depends on the function signature. Its essentially a wrapper for a pointer
/// and should only be used as such.
///
/// So, don't move this thing around. I would wrap it in a `Pin`, but `Pin` is
/// annoying to use, so all the functions are just unsafe instead.
#[repr(C)]
pub struct RebarArgs {
  _phantom: PhantomPinned,
}

impl RebarArgs {
  pub unsafe fn arg(&self, offset: usize) -> *const i64 {
    unsafe {
      let ptr = self as *const _;
      (ptr as *const i64).offset(offset as isize)
    }
  }

  pub unsafe fn ret(&mut self, offset: usize, value: i64) {
    unsafe {
      let ptr = self as *mut _;
      *(ptr as *mut i64).offset(offset as isize) = value
    }
  }
}

pub struct RuntimeHelpers {
  pub call: fn(i64, *const RebarArgs, *mut RebarArgs),

  pub push_frame: fn(),
  pub pop_frame:  fn(),
}

const DEBUG: bool = false;

impl JIT {
  #[allow(clippy::new_without_default)]
  pub fn new(helpers: RuntimeHelpers) -> Self {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    flag_builder.set("opt_level", "speed_and_size").unwrap();
    let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
      panic!("host machine is not supported: {}", msg);
    });
    let isa = isa_builder.finish(settings::Flags::new(flag_builder)).unwrap();
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

    builder.symbol("__call", helpers.call as *const _);
    builder.symbol("__push_frame", helpers.push_frame as *const _);
    builder.symbol("__pop_frame", helpers.pop_frame as *const _);

    let mut module = JITModule::new(builder);

    let mut call_sig = module.make_signature();
    call_sig.params.push(AbiParam::new(ir::types::I64));
    call_sig.params.push(AbiParam::new(ir::types::I64));
    call_sig.params.push(AbiParam::new(ir::types::I64));

    let push_frame_sig = module.make_signature();
    let pop_frame_sig = module.make_signature();

    JIT {
      data_description: DataDescription::new(),
      funcs: NativeFuncs {
        call:       module.declare_function("__call", Linkage::Import, &call_sig).unwrap(),
        push_frame: module
          .declare_function("__push_frame", Linkage::Import, &push_frame_sig)
          .unwrap(),
        pop_frame:  module
          .declare_function("__pop_frame", Linkage::Import, &pop_frame_sig)
          .unwrap(),
      },
      module,
      user_funcs: HashMap::new(),
    }
  }

  pub fn new_thread(&self) -> ThreadCtx {
    let ctx = self.module.make_context();

    ThreadCtx {
      builder_context: FunctionBuilderContext::new(),
      ctx,
      isa: self.module.isa(),

      funcs: self.funcs(),
      user_funcs: &self.user_funcs,
    }
  }

  fn funcs(&self) -> NativeFuncs<NativeFuncDecl> {
    self
      .funcs
      .map(|id| NativeFuncDecl { id, decl: self.module.declarations().get_function_decl(id) })
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

    let mut index = 0;
    let funcs = self.funcs.map(|func| {
      let signature = builder.func.import_signature(func.decl.signature.clone());
      let user_name_ref =
        builder.func.declare_imported_user_function(ir::UserExternalName { namespace: 0, index });
      index += 1;
      let colocated = func.decl.linkage.is_final();
      builder.func.import_function(ir::ExtFuncData {
        name: ir::ExternalName::user(user_name_ref),
        signature,
        colocated,
      })
    });

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

    FuncBuilder { builder, mir, funcs, locals: HashMap::new(), next_variable: 0, user_funcs }
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
  fn translate(mut self) {
    let entry_block = self.builder.create_block();

    let mut param_values = vec![];

    for ty in self.mir.params.iter() {
      match ParamKind::for_type(ty) {
        ParamKind::Zero => {
          param_values.push(CompactValues::None);
        }
        ParamKind::Compact => {
          let value = self.builder.append_block_param(entry_block, ir::types::I64);
          param_values.push(CompactValues::One(value));
        }
        ParamKind::Extended => {
          let v0 = self.builder.append_block_param(entry_block, ir::types::I64);
          let v1 = self.builder.append_block_param(entry_block, ir::types::I64);
          param_values.push(CompactValues::Two(v0, v1));
        }
      }
    }

    if let Some(ref ty) = self.mir.ret {
      match ParamKind::for_type(ty) {
        ParamKind::Extended => todo!("Extended variables not supported for parameters yet"),
        _ => {}
      }

      assert!(self.builder.func.signature.returns.len() == 1);
    } else {
      assert!(self.builder.func.signature.returns.is_empty());
    }

    self.builder.switch_to_block(entry_block);
    self.builder.seal_block(entry_block);

    self.builder.ins().call(self.funcs.push_frame, &[]);

    for (id, param) in param_values.into_iter().enumerate() {
      let len = param.len();
      let variables = (0..len).map(|_| self.new_variable()).collect::<Vec<_>>();
      let values = param.with_slice(|s| s.to_vec());

      self.locals.insert(mir::VarId(id as u32), variables.clone());
      self.set_var(&variables, &values);
    }

    for &stmt in &self.mir.items {
      let _res = self.compile_stmt(stmt);
      // self.def_var(return_variable, res.to_ir());
    }

    self.builder.ins().call(self.funcs.pop_frame, &[]);

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

impl JIT {
  pub fn declare_function(&mut self, func: &mir::Function) {
    let mut sig = self.module.make_signature();

    sig.call_conv = CallConv::Fast;
    for ty in func.params.iter() {
      match ParamKind::for_type(ty) {
        ParamKind::Zero => {}
        ParamKind::Compact => sig.params.push(AbiParam::new(ir::types::I64)),
        ParamKind::Extended => {
          sig.params.push(AbiParam::new(ir::types::I64));
          sig.params.push(AbiParam::new(ir::types::I64));
        }
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

// FIXME: Wrap `InstBuilder` so this is easier.
fn use_var(builder: &mut FunctionBuilder, var: &[Variable]) -> RValue {
  match var {
    [] => RValue::nil(),

    // TODO: Need to get the static type in here and use that.
    [var] => {
      let ir = builder.use_var(*var);
      RValue { ty: Value::Const(ValueType::Int), values: vec![Value::Dyn(ir)] }
    }

    [ty, value @ ..] => {
      if value.len() != 1 {
        todo!("multiple value variables");
      }

      let ty = builder.use_var(*ty);
      let value = builder.use_var(value[0]);

      RValue { ty: Value::Dyn(ty), values: vec![Value::Dyn(value)] }
    }
  }
}

impl FuncBuilder<'_> {
  fn new_variable(&mut self) -> Variable {
    let var = Variable::new(self.next_variable);
    self.builder.declare_var(var, ir::types::I64);
    self.next_variable += 1;
    var
  }

  fn set_var(&mut self, var: &[Variable], ir: &[ir::Value]) {
    if var.is_empty() && ir.is_empty() {
      return;
    }

    assert!(!ir.is_empty(), "ir must have at least one element, got {ir:?}");

    // The first value is the only one that must be set. For example, if a value is
    // set to `nil`, the second variable is undefined.
    for (&var, &value) in var.iter().zip(ir.iter()) {
      self.builder.def_var(var, value);
    }
  }

  fn compile_stmt(&mut self, stmt: mir::StmtId) -> RValue {
    match self.mir.stmts[stmt] {
      mir::Stmt::Expr(expr) => self.compile_expr(expr),
      mir::Stmt::Let(id, ref ty, expr) => {
        let value = self.compile_expr(expr);
        let ir = value.to_ir(ParamKind::for_type(&ty), &mut self.builder);

        let variables = ir.iter().map(|_| self.new_variable()).collect::<Vec<_>>();

        self.set_var(&variables, &ir);
        self.locals.insert(id, variables);

        self.track_value(value, ty);

        RValue::nil()
      }
    }
  }

  /// Track a value in the GC stack. When the current function returns, the
  /// value will be untracked.
  fn track_value(&mut self, value: RValue, ty: &Type) {
    if self.type_needs_gc(ty) {
      // let native = value.to_ir(&mut self.builder);
      // self.builder.ins().call(self.funcs.track, &[native, arg_ptr, ret_ptr]);
    }
  }

  fn type_needs_gc(&self, ty: &Type) -> bool {
    match ty {
      Type::Literal(Literal::Unit) => false,
      Type::Literal(Literal::Int) => false,
      Type::Literal(Literal::Bool) => false,
      Type::Literal(Literal::String) => true,
      Type::Union(vs) => vs.iter().any(|v| self.type_needs_gc(v)),

      // TODO: uhhhhhhhhhh
      Type::Function(..) => false,
    }
  }

  fn compile_expr(&mut self, expr: mir::ExprId) -> RValue {
    match self.mir.exprs[expr] {
      mir::Expr::Literal(ref lit) => match lit {
        mir::Literal::Nil => RValue::nil(),
        mir::Literal::Bool(v) => RValue::bool(self.builder.ins().iconst(ir::types::I8, *v as i64)),
        mir::Literal::Int(i) => RValue::int(self.builder.ins().iconst(ir::types::I64, *i)),
        mir::Literal::String(i) => {
          // Note that we don't care about alignment here: we handle reading an unaligned
          // i64.
          let to_leak = i.clone();

          let len = to_leak.len();
          let cap = to_leak.capacity();
          let ptr = to_leak.as_ptr();

          // TODO: Throw this in a GC or something.
          String::leak(to_leak);

          RValue {
            ty:     Value::Const(ValueType::String),
            values: vec![Value::from(len as i64), Value::from(cap as i64), Value::from(ptr as i64)],
          }
        }
      },

      mir::Expr::Local(id) => use_var(&mut self.builder, &self.locals[&id]),

      mir::Expr::UserFunction(id, _) => RValue {
        ty:     Value::Const(ValueType::UserFunction),
        values: vec![Value::Const(id.0 as i64)],
      },

      mir::Expr::Native(ref id, _) => {
        RValue::function(self.builder.ins().iconst(ir::types::I64, id.0 as i64))
      }

      mir::Expr::Block(ref stmts) => {
        // FIXME: Make a new scope so that locals don't leak.
        let mut return_value = RValue::nil();
        for &stmt in stmts {
          return_value = self.compile_stmt(stmt);
        }
        return_value
      }

      mir::Expr::Call(lhs, ref sig_ty, ref args) => {
        let lhs = self.compile_expr(lhs);

        match lhs.ty.as_const() {
          Some(ValueType::Function) => {
            let arg_types = match sig_ty {
              Type::Function(ref args, _) => args,
              _ => unreachable!(),
            };

            assert_eq!(args.len(), arg_types.len());

            // Argument length in 8 byte increments.
            let mut arg_len = 0;
            let mut arg_values = vec![];
            for (&arg, arg_ty) in args.iter().zip(arg_types.iter()) {
              let arg = self.compile_expr(arg);

              let v = arg.to_ir(ParamKind::for_type(arg_ty), &mut self.builder);
              arg_len += v.len();
              arg_values.push(v);
            }

            // FIXME: This needs to be more generic.
            let ret_len = match *sig_ty {
              Type::Function(_, ref ret) => match **ret {
                Type::Literal(Literal::Unit) => 0,
                Type::Literal(Literal::Int) => 1,
                Type::Literal(Literal::String) => 3,
                _ => unimplemented!("return type {ret:?}"),
              },
              _ => unreachable!(),
            };

            let arg_slot = self.builder.create_sized_stack_slot(StackSlotData {
              kind: StackSlotKind::ExplicitSlot,
              // Each argument is 8 bytes wide.
              size: arg_len as u32 * 8,
            });
            let ret_slot = self.builder.create_sized_stack_slot(StackSlotData {
              kind: StackSlotKind::ExplicitSlot,
              // Each return value is 8 bytes wide.
              size: ret_len as u32 * 8,
            });

            let mut slot_index = 0;
            for v in arg_values {
              for &v in v.iter() {
                self.builder.ins().stack_store(v, arg_slot, slot_index * 8);
                slot_index += 1;
              }
            }

            let arg_ptr = self.builder.ins().stack_addr(ir::types::I64, arg_slot, 0);
            let ret_ptr = self.builder.ins().stack_addr(ir::types::I64, ret_slot, 0);

            let native = lhs.values[0].to_ir(&mut self.builder);
            self.builder.ins().call(self.funcs.call, &[native, arg_ptr, ret_ptr]);

            match *sig_ty {
              Type::Function(_, ref ret) => match **ret {
                Type::Literal(Literal::Unit) => RValue::nil(),
                Type::Literal(Literal::Int) => {
                  RValue::int(self.builder.ins().stack_load(ir::types::I64, ret_slot, 0))
                }
                Type::Literal(Literal::String) => RValue {
                  ty:     Value::Const(ValueType::String),
                  values: vec![
                    Value::from(self.builder.ins().stack_load(ir::types::I64, ret_slot, 0)),
                    Value::from(self.builder.ins().stack_load(ir::types::I64, ret_slot, 8)),
                    Value::from(self.builder.ins().stack_load(ir::types::I64, ret_slot, 16)),
                  ],
                },
                _ => unimplemented!("return type {ret:?}"),
              },
              _ => unreachable!(),
            }
          }

          Some(ValueType::UserFunction) => {
            let id = match lhs.values[0] {
              Value::Const(v) => UserFunctionId(v as u64),
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

              let v = arg.to_ir(ParamKind::for_type(arg_ty), &mut self.builder);
              for v in v {
                use cranelift::codegen::ir::InstBuilderBase;

                match self.builder.ins().data_flow_graph_mut().value_type(v) {
                  ir::types::I64 => arg_values.push(v),
                  _ => {
                    let v2 = self.builder.ins().uextend(ir::types::I64, v);
                    arg_values.push(v2);
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
        let lhs = lhs.values[0].to_ir(&mut self.builder); // FIXME: Don't just grab index 0.

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
            let lhs = lhs.values[0].to_ir(&mut self.builder);
            let rhs = rhs.values[0].to_ir(&mut self.builder);

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

          mir::BinaryOp::Eq | mir::BinaryOp::Neq => match (lhs.ty.as_const(), rhs.ty.as_const()) {
            (Some(ValueType::Nil), Some(ValueType::Nil)) => {
              let tru = self.builder.ins().iconst(ir::types::I8, 1);
              RValue::bool(tru)
            }
            (Some(ValueType::Bool), Some(ValueType::Bool)) => {
              let l = lhs.values[0].to_ir(&mut self.builder);
              let r = rhs.values[0].to_ir(&mut self.builder);

              let res = match op {
                mir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, l, r),
                mir::BinaryOp::Neq => self.builder.ins().icmp(IntCC::NotEqual, l, r),
                _ => unreachable!(),
              };

              RValue::bool(res)
            }
            (Some(ValueType::Int), Some(ValueType::Int)) => {
              let l = lhs.values[0].to_ir(&mut self.builder);
              let r = rhs.values[0].to_ir(&mut self.builder);

              let res = match op {
                mir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, l, r),
                mir::BinaryOp::Neq => self.builder.ins().icmp(IntCC::NotEqual, l, r),
                _ => unreachable!(),
              };

              RValue::bool(res)
            }
            (Some(ValueType::String), Some(ValueType::String)) => {
              let l_len = lhs.values[0].to_ir(&mut self.builder);
              // let _l_ptr = rhs.values[2].to_ir(&mut self.builder);
              let r_len = rhs.values[0].to_ir(&mut self.builder);
              // let _r_ptr = rhs.values[2].to_ir(&mut self.builder);

              let res = match op {
                mir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, l_len, r_len),
                mir::BinaryOp::Neq => self.builder.ins().icmp(IntCC::NotEqual, l_len, r_len),
                _ => unreachable!(),
              };

              RValue::bool(res)
            }

            (Some(a), Some(b)) if a != b => RValue::bool(false as i64),

            // TODO: Theres a couple more branches we could optimize for here, but the dynamic path
            // is nice to fall back on.
            (_, _) => {
              let l_ty = lhs.ty.to_ir(&mut self.builder);
              let r_ty = rhs.ty.to_ir(&mut self.builder);
              let l_val = lhs.values.get(0).map(|v| v.to_ir(&mut self.builder));
              let r_val = rhs.values.get(0).map(|v| v.to_ir(&mut self.builder));

              let res = match op {
                mir::BinaryOp::Eq => match (l_val, r_val) {
                  (Some(l), Some(r)) => {
                    let ty_eq = self.builder.ins().icmp(IntCC::Equal, l_ty, r_ty);
                    let v_eq = self.builder.ins().icmp(IntCC::Equal, l, r);
                    self.builder.ins().band(ty_eq, v_eq)
                  }
                  // This is handles the union case. For example the left could be `int | nil`, and
                  // the right could be `nil`. In this case, we can just compare types.
                  _ => self.builder.ins().icmp(IntCC::Equal, l_ty, r_ty),
                },
                mir::BinaryOp::Neq => match (l_val, r_val) {
                  (Some(l), Some(r)) => {
                    let ty_eq = self.builder.ins().icmp(IntCC::NotEqual, l_ty, r_ty);
                    let v_eq = self.builder.ins().icmp(IntCC::NotEqual, l, r);
                    self.builder.ins().bor(ty_eq, v_eq)
                  }
                  _ => self.builder.ins().icmp(IntCC::NotEqual, l_ty, r_ty),
                },
                _ => unreachable!(),
              };

              RValue::bool(res)
            }
          },

          _ => {
            let lhs = lhs.values[0].to_ir(&mut self.builder);
            let rhs = rhs.values[0].to_ir(&mut self.builder);

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

      mir::Expr::If { cond, then, els: None, ty: _ } => {
        let cond = self.compile_expr(cond);
        let cond = cond.values[0].to_ir(&mut self.builder);

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
        let cond = cond.values[0].to_ir(&mut self.builder);

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        let param_kind = ParamKind::for_type(ty);
        param_kind.append_block_params(&mut self.builder, merge_block);

        // Test the if condition and conditionally branch.
        self.builder.ins().brif(cond, then_block, &[], else_block, &[]);

        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        let then_return = self.compile_expr(then).to_ir(param_kind, &mut self.builder);

        // Jump to the merge block, passing it the block return value.
        self.builder.ins().jump(merge_block, &then_return);

        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        let else_return = self.compile_expr(els).to_ir(param_kind, &mut self.builder);

        // Jump to the merge block, passing it the block return value.
        self.builder.ins().jump(merge_block, &else_return);

        // Switch to the merge block for subsequent statements.
        self.builder.switch_to_block(merge_block);

        // We've now seen all the predecessors of the merge block.
        self.builder.seal_block(merge_block);

        // Read the value of the if-else by reading the merge block
        // parameter.
        RValue::from_ir(self.builder.block_params(merge_block), ty)
      }

      ref v => unimplemented!("expr: {v:?}"),
    }
  }
}
