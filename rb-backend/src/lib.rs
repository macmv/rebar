use codegen::{
  control::ControlPlane,
  ir::{self, FuncRef},
  CompiledCode,
};
use cranelift::prelude::*;
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use isa::{CallConv, TargetFrontendConfig, TargetIsa};
use rb_mir::{
  ast::{self as mir, UserFunctionId},
  MirContext,
};
use rb_typer::{Literal, Type};
use slot::Slot;
use std::{collections::HashMap, io::BufWriter};

mod r_value;
mod slot;

use r_value::RValue;

use rb_value::{DynamicValueType, IntrinsicImpls, ValueType};

pub struct Compiler {
  mir_ctx: MirContext,
  module:  ObjectModule,

  // TODO: Use this for string literals at the very least.
  #[allow(dead_code)]
  data_description: DataDescription,

  user_funcs: HashMap<mir::UserFunctionId, (FuncId, Signature)>,
}

pub struct ThreadCtx<'a> {
  mir_ctx:         &'a MirContext,
  builder_context: FunctionBuilderContext,
  ctx:             codegen::Context,

  isa: &'a dyn TargetIsa,

  user_funcs: &'a HashMap<mir::UserFunctionId, (FuncId, Signature)>,
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
      pub fn prepare(_builder: &mut ObjectBuilder, _impls: &IntrinsicImpls) {
        // $(
        //   builder.symbol(concat!("__", stringify!($name)), impls.$name as *const _);
        // )*
      }

      pub fn build(module: &mut ObjectModule) -> Self {
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
);

pub struct FuncBuilder<'a> {
  ctx: &'a MirContext,
  isa: &'a dyn TargetIsa,

  builder: FunctionBuilder<'a>,
  mir:     &'a mir::Function,

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
  pub fn new(mir_ctx: MirContext) -> Self {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    flag_builder.set("opt_level", "speed_and_size").unwrap();
    let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
      panic!("host machine is not supported: {}", msg);
    });
    let isa = isa_builder.finish(settings::Flags::new(flag_builder)).unwrap();
    let builder =
      ObjectBuilder::new(isa, "foo", cranelift_module::default_libcall_names()).unwrap();

    let module = ObjectModule::new(builder);

    Compiler {
      mir_ctx,
      data_description: DataDescription::new(),
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

      user_funcs: &self.user_funcs,
    }
  }

  pub fn finish(self) {
    let object = self.module.finish();

    let out = std::fs::File::create("out.o").unwrap();
    object.object.write_stream(BufWriter::new(out)).unwrap();

    let status = std::process::Command::new("wild").arg("out.o").status().unwrap();
    if !status.success() {
      panic!("linker failed");
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
      builder,
      mir,
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

    let name = if func.id.0 == 0 { "_start".into() } else { format!("foooo_{}", func.id.0) };

    let id = self.module.declare_function(&name, Linkage::Export, &sig).unwrap();
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

        RValue::nil()
      }
    }
  }

  fn compile_expr(&mut self, expr: mir::ExprId) -> RValue {
    match self.mir.exprs[expr] {
      mir::Expr::Literal(ref lit) => match lit {
        mir::Literal::Nil => RValue::nil(),
        mir::Literal::Bool(v) => RValue::bool(self.builder.ins().iconst(ir::types::I8, *v as i64)),
        mir::Literal::Int(i) => RValue::int(self.builder.ins().iconst(ir::types::I64, *i)),
        mir::Literal::String(_) => todo!("string literals"),
      },

      mir::Expr::StringInterp(_) => todo!("interpolated strings"),

      mir::Expr::Array(_, _) => todo!("array literals"),

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
        let mut return_value = RValue::nil();

        for &stmt in stmts {
          return_value = self.compile_stmt(stmt);
        }

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

            (_, _) => todo!("equality for {lhs:?} and {rhs:?}"),
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
    _native: ir::Value,
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

    let _arg_ptr = self.builder.ins().stack_addr(ir::types::I64, arg_slot, 0);
    let _ret_ptr = self.builder.ins().stack_addr(ir::types::I64, ret_slot, 0);

    // self.call_intrinsic(intrinsic::call, &[native, arg_ptr, ret_ptr]);

    match ret_dvt {
      DynamicValueType::Const(vt) => {
        RValue::TypedDyn(vt, Slot::Multiple(ret_dvt.len(self.ctx) as usize, ret_slot))
      }
      DynamicValueType::Union(_) => {
        RValue::Untyped(Slot::Multiple(ret_dvt.len(self.ctx) as usize, ret_slot))
      }
    }
  }
}
