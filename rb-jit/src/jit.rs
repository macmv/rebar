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
use std::{collections::HashMap, marker::PhantomPinned, mem::ManuallyDrop};

use crate::value::{CompactValues, DynamicValueType, ParamKind, RValue, Value, ValueType};

pub struct JIT {
  module: JITModule,

  // TODO: Use this for string literals at the very least.
  #[allow(dead_code)]
  data_description: DataDescription,

  intrinsics: Intrinsics<FuncId>,
  user_funcs: HashMap<mir::UserFunctionId, (FuncId, Signature)>,
}

pub struct ThreadCtx<'a> {
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

macro_rules! intrinsics {
  ($(
    $name:ident($($arg:ident),*) $(-> $ret:ident)?,
  )*) => {
    pub struct Intrinsics<T> {
      $($name: T),*
    }

    impl<T: Copy> Intrinsics<T> {
      fn map<U>(&self, mut f: impl FnMut(T) -> U) -> Intrinsics<U> {
        Intrinsics {
          $($name: f(self.$name)),*
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
  call(I64, I64, I64),
  push_frame(),
  pop_frame(),
  track(I64),
  string_append_value(I64, I64),
  array_push(I64, I64, I64),
  array_index(I64, I64, I64),
  value_equals(I64, I64) -> I8,
);

pub struct FuncBuilder<'a> {
  builder:    FunctionBuilder<'a>,
  mir:        &'a mir::Function,
  intrinsics: Intrinsics<FuncRef>,

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

pub struct IntrinsicImpls {
  pub call: fn(i64, *const RebarArgs, *mut RebarArgs),

  pub push_frame:          fn(),
  pub pop_frame:           fn(),
  pub track:               fn(*const RebarArgs),
  pub string_append_value: fn(*const RebarArgs, *const RebarArgs),
  pub array_push:          fn(*mut Vec<i64>, i64, *const RebarArgs),
  pub array_index:         fn(*const RebarArgs, *const RebarArgs, *mut RebarArgs),
  pub value_equals:        fn(*const RebarArgs, *const RebarArgs) -> i8,
}

const DEBUG: bool = false;

impl JIT {
  #[allow(clippy::new_without_default)]
  pub fn new(intrinsics: IntrinsicImpls) -> Self {
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

    JIT {
      data_description: DataDescription::new(),
      intrinsics: Intrinsics::build(&mut module),
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

      intrinsics: self.intrinsics(),
      user_funcs: &self.user_funcs,
    }
  }

  fn intrinsics(&self) -> Intrinsics<IntrinsicDecl> {
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

    let mut index = 0;
    let funcs = self.intrinsics.map(|func| {
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

    FuncBuilder {
      builder,
      mir,
      intrinsics: funcs,
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
  fn translate(mut self) {
    let entry_block = self.builder.create_block();

    let mut param_values = vec![];

    for ty in self.mir.params.iter() {
      match DynamicValueType::for_type(ty) {
        DynamicValueType::Const(_) => {
          let value = self.builder.append_block_param(entry_block, ir::types::I64);
          param_values.push(CompactValues::One(value));
        }
        DynamicValueType::Union(_) => {
          let v0 = self.builder.append_block_param(entry_block, ir::types::I64);
          let v1 = self.builder.append_block_param(entry_block, ir::types::I64);
          param_values.push(CompactValues::Two(v0, v1));
        }
      }
    }

    if let Some(ref ty) = self.mir.ret {
      match DynamicValueType::for_type(ty) {
        DynamicValueType::Union(_) => todo!("Extended variables not supported for parameters yet"),
        _ => {}
      }

      assert!(self.builder.func.signature.returns.len() == 1);
    } else {
      assert!(self.builder.func.signature.returns.is_empty());
    }

    self.builder.switch_to_block(entry_block);
    self.builder.seal_block(entry_block);

    self.builder.ins().call(self.intrinsics.push_frame, &[]);

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

    self.builder.ins().call(self.intrinsics.pop_frame, &[]);

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
      let dvt = DynamicValueType::for_type(ty);
      for _ in 0..dvt.len() {
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

// FIXME: Wrap `InstBuilder` so this is easier.
fn use_var(builder: &mut FunctionBuilder, var: &[Variable], ty: &Type) -> RValue {
  let dvt = DynamicValueType::for_type(ty);
  assert_eq!(var.len() as u32, dvt.len(), "variable length mismatch for type {ty:?}");

  match dvt {
    DynamicValueType::Const(ty) => RValue {
      ty:     Value::Const(ty),
      values: var.iter().map(|v| Value::Dyn(builder.use_var(*v))).collect::<Vec<_>>(),
    },

    DynamicValueType::Union(_) => RValue {
      ty:     Value::Dyn(builder.use_var(var[0])),
      values: var[1..].iter().map(|v| Value::Dyn(builder.use_var(*v))).collect::<Vec<_>>(),
    },
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
        let ir = value.to_ir(DynamicValueType::for_type(&ty).param_kind(), &mut self.builder);

        let variables = ir.iter().map(|_| self.new_variable()).collect::<Vec<_>>();

        self.set_var(&variables, &ir);
        self.locals.insert(id, variables);

        if self.type_needs_gc(ty) {
          self.track_value(&value);
        }

        RValue::nil()
      }
    }
  }

  /// Track a value in the GC stack. When the current function returns, the
  /// value will be untracked.
  fn track_value(&mut self, value: &RValue) {
    let arg_ptr = self.stack_slot_unsized(&value);

    self.builder.ins().call(self.intrinsics.track, &[arg_ptr]);
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
          let mut to_leak = i.clone();
          to_leak.shrink_to_fit();

          let len = to_leak.len();
          let ptr = to_leak.as_ptr();

          // TODO: Throw this in a GC or something.
          String::leak(to_leak);

          RValue {
            ty:     Value::Const(ValueType::String),
            values: vec![Value::from(len as i64), Value::from(ptr as i64)],
          }
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
        let result_str = ManuallyDrop::new(String::new());

        let len = result_str.len();
        let cap = result_str.capacity();
        let ptr = result_str.as_ptr();

        // NB: This slot is mutated! We're using it to append to the string.
        let str_slot = self.builder.create_sized_stack_slot(StackSlotData {
          kind: StackSlotKind::ExplicitSlot,
          // A string is composed of 3 values, each being 8 bytes.
          size: 3 * 8,
        });
        let len = self.builder.ins().iconst(ir::types::I64, len as i64);
        let cap = self.builder.ins().iconst(ir::types::I64, cap as i64);
        let ptr = self.builder.ins().iconst(ir::types::I64, ptr as i64);
        self.builder.ins().stack_store(len, str_slot, 0);
        self.builder.ins().stack_store(cap, str_slot, 8);
        self.builder.ins().stack_store(ptr, str_slot, 16);

        let str_addr = self.builder.ins().stack_addr(ir::types::I64, str_slot, 0);

        for segment in segments {
          let to_append = match segment {
            mir::StringInterp::Literal(str) => {
              let mut to_leak = String::from(str);
              to_leak.shrink_to_fit();

              let len = to_leak.len();
              let ptr = to_leak.as_ptr();

              // TODO: Throw this in a memoized pool of string literals.
              String::leak(to_leak);

              RValue {
                ty:     Value::Const(ValueType::String),
                values: vec![Value::from(len as i64), Value::from(ptr as i64)],
              }
            }

            mir::StringInterp::Expr(e) => self.compile_expr(*e),
          };

          let arg_ptr = self.stack_slot_unsized(&to_append);

          self.builder.ins().call(self.intrinsics.string_append_value, &[str_addr, arg_ptr]);
        }

        // Now that we're done mutating the slot, we can track the value in the GC (and
        // we can drop the `cap` amount, because we don't need that anymore, now that
        // the string is immutable).
        let result = RValue {
          ty:     Value::Const(ValueType::String),
          values: vec![
            // Len
            Value::Dyn(self.builder.ins().stack_load(ir::types::I64, str_slot, 0)),
            // Ptr
            Value::Dyn(self.builder.ins().stack_load(ir::types::I64, str_slot, 16)),
          ],
        };

        self.track_value(&result);

        result
      }

      mir::Expr::Array(ref exprs, ref ty) => {
        let vt = DynamicValueType::for_type(ty);
        let slot_size = vt.len();

        let result_box = Box::<Vec<i64>>::new(vec![0; slot_size as usize * exprs.len()]);
        let array_ptr = result_box.as_ptr();

        for (i, expr) in exprs.iter().enumerate() {
          let to_append = self.compile_expr(*expr);
          let ir = to_append.to_ir(vt.param_kind(), &mut self.builder);
          assert_eq!(ir.len(), slot_size as usize);

          unsafe {
            let element_ptr = array_ptr.offset(i as isize * slot_size as isize);
            let element_ptr = self.builder.ins().iconst(ir::types::I64, element_ptr as i64);

            // TODO: Compile this into a loop if its too long.
            for j in 0..slot_size as usize {
              self.builder.ins().store(MemFlags::new(), ir[j], element_ptr, (j as i32) * 8);
            }
          }
        }

        let result_ptr =
          self.builder.ins().iconst(ir::types::I64, Box::into_raw(result_box) as i64);

        let result = RValue {
          ty:     Value::Const(ValueType::Array),
          values: vec![Value::Dyn(result_ptr), Value::Const(vt.encode())],
        };

        self.track_value(&result);

        result
      }

      mir::Expr::Local(id, ref ty) => use_var(&mut self.builder, &self.locals[&id], ty),

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

            // Argument length in 8 byte increments.
            let mut arg_values = vec![];
            for (&arg, arg_ty) in args.iter().zip(arg_types.iter()) {
              let arg = self.compile_expr(arg);

              let v =
                arg.to_ir(DynamicValueType::for_type(&arg_ty).param_kind(), &mut self.builder);
              arg_values.push(v);
            }

            let native = lhs.values[0].to_ir(&mut self.builder);

            let ret_ty = match *sig_ty {
              Type::Function(_, ref ret) => ret,
              _ => unreachable!(),
            };

            self.call_native(native, &arg_values, arg_types, &**ret_ty)
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

              let v =
                arg.to_ir(DynamicValueType::for_type(&arg_ty).param_kind(), &mut self.builder);
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

            (Some(a), Some(b)) if a != b => RValue::bool(false as i64),

            // TODO: Theres a couple more branches we could optimize for here, but the dynamic path
            // is nice to fall back on.
            (_, _) => {
              let l_addr = self.stack_slot_unsized(&lhs);
              let r_addr = self.stack_slot_unsized(&rhs);

              let ret = self.builder.ins().call(self.intrinsics.value_equals, &[l_addr, r_addr]);

              RValue::bool(self.builder.inst_results(ret)[0])
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

      mir::Expr::Index(lhs, rhs, ref ret_ty) => {
        let lhs = self.compile_expr(lhs);
        let rhs = self.compile_expr(rhs);

        let ret_dvt = DynamicValueType::for_type(ret_ty);

        let l_addr = self.stack_slot_unsized(&lhs);
        let r_addr = self.stack_slot_unsized(&rhs);

        let ret_slot = self.builder.create_sized_stack_slot(StackSlotData {
          kind: StackSlotKind::ExplicitSlot,
          // Each return value is 8 bytes wide.
          size: ret_dvt.len() * 8,
        });
        let ret_ptr = self.builder.ins().stack_addr(ir::types::I64, ret_slot, 0);

        self.builder.ins().call(self.intrinsics.array_index, &[l_addr, r_addr, ret_ptr]);

        match ret_dvt {
          DynamicValueType::Const(vt) => RValue {
            ty:     Value::Const(vt),
            values: (0..vt.len())
              .map(|i| {
                Value::from(self.builder.ins().stack_load(ir::types::I64, ret_slot, i as i32 * 8))
              })
              .collect(),
          },
          DynamicValueType::Union(len) => RValue {
            ty:     Value::Dyn(self.builder.ins().stack_load(ir::types::I64, ret_slot, 0)),
            // NB: Use `len`, not `ret_dvt.len()`, because we're reading the union tag by hand
            // above.
            values: (0..len)
              .map(|i| {
                Value::Dyn(self.builder.ins().stack_load(
                  ir::types::I64,
                  ret_slot,
                  i as i32 * 8 + 8,
                ))
              })
              .collect(),
          },
        }
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

        let dvt = DynamicValueType::for_type(&ty);
        dvt.append_block_params(&mut self.builder, merge_block);
        let param_kind = dvt.param_kind();

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

  fn call_native(
    &mut self,
    native: ir::Value,
    args: &[Vec<ir::Value>],
    arg_types: &[Type],
    ret_ty: &Type,
  ) -> RValue {
    assert_eq!(args.len(), arg_types.len());

    let ret_dvt = DynamicValueType::for_type(ret_ty);

    let arg_len = args.iter().map(|v| v.len()).sum::<usize>();

    let arg_slot = self.builder.create_sized_stack_slot(StackSlotData {
      kind: StackSlotKind::ExplicitSlot,
      // Each argument is 8 bytes wide.
      size: arg_len as u32 * 8,
    });
    let ret_slot = self.builder.create_sized_stack_slot(StackSlotData {
      kind: StackSlotKind::ExplicitSlot,
      // Each return value is 8 bytes wide.
      size: ret_dvt.len() * 8,
    });

    let mut slot_index = 0;
    for v in args {
      for &v in v.iter() {
        self.builder.ins().stack_store(v, arg_slot, slot_index * 8);
        slot_index += 1;
      }
    }

    let arg_ptr = self.builder.ins().stack_addr(ir::types::I64, arg_slot, 0);
    let ret_ptr = self.builder.ins().stack_addr(ir::types::I64, ret_slot, 0);

    self.builder.ins().call(self.intrinsics.call, &[native, arg_ptr, ret_ptr]);

    match ret_dvt {
      DynamicValueType::Const(vt) => RValue {
        ty:     Value::Const(ValueType::String),
        values: (0..vt.len())
          .map(|i| {
            Value::from(self.builder.ins().stack_load(ir::types::I64, ret_slot, i as i32 * 8))
          })
          .collect(),
      },
      DynamicValueType::Union(len) => RValue {
        ty:     Value::Dyn(self.builder.ins().stack_load(ir::types::I64, ret_slot, 0)),
        // NB: Use `len`, not `ret_dvt.len()`, because we're reading the union tag by hand above.
        values: (0..len)
          .map(|i| {
            Value::Dyn(self.builder.ins().stack_load(ir::types::I64, ret_slot, i as i32 * 8 + 8))
          })
          .collect(),
      },
    }
  }

  /// Creates a stack slot that stores a single unsized value, and returns the
  /// address to that slot. Used when calling native functions.
  fn stack_slot_unsized(&mut self, value: &RValue) -> ir::Value {
    let ir = value.to_ir(ParamKind::Extended(None), &mut self.builder);

    self.stack_slot_for_ir(ir)
  }

  /// Creates a stack slot that stores a single value, sized to the given
  /// DynamicValueType.
  fn stack_slot_sized(&mut self, value: &RValue, vt: DynamicValueType) -> ir::Value {
    let ir = value.to_ir(vt.param_kind(), &mut self.builder);

    self.stack_slot_for_ir(ir)
  }

  fn stack_slot_for_ir(&mut self, ir: Vec<ir::Value>) -> ir::Value {
    let slot = self.builder.create_sized_stack_slot(StackSlotData {
      kind: StackSlotKind::ExplicitSlot,
      size: ir.len() as u32 * 8,
    });

    for (i, &v) in ir.iter().enumerate() {
      self.builder.ins().stack_store(v, slot, i as i32 * 8);
    }

    self.builder.ins().stack_addr(ir::types::I64, slot, 0)
  }
}
