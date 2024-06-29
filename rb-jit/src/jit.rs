use codegen::{
  control::ControlPlane,
  ir::{self, FuncRef},
  CompiledCode, FinalizedMachReloc,
};
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, FunctionDeclaration, Linkage, Module};
use isa::TargetIsa;
use rb_mir::ast as mir;
use rb_typer::{Literal, Type};
use std::{collections::HashMap, marker::PhantomPinned};

pub struct JIT {
  module: JITModule,

  // TODO: Use this for string literals at the very least.
  #[allow(dead_code)]
  data_description: DataDescription,

  call_func: FuncId,
}

pub struct ThreadCtx<'a> {
  builder_context: FunctionBuilderContext,
  ctx:             codegen::Context,

  isa:            &'a dyn TargetIsa,
  call_func:      FuncId,
  call_func_decl: &'a FunctionDeclaration,
}

pub struct FuncBuilder<'a> {
  builder:       FunctionBuilder<'a>,
  mir:           &'a mir::Function,
  call_func_ref: FuncRef,

  // Note that `VarId` and `Variable` are entirely distinct.
  //
  // `VarId` is an opaque identifier for a local variable in the AST, whereas `Variable` is a
  // cranelift IR variable. There will usually be more cranelift variables than local variables.
  locals:        HashMap<mir::VarId, Variable>,
  next_variable: usize,
}

/// This struct is horribly dangerous to use.
///
/// It should only be constructed from within the rebar runtime. The layout
/// should look something like this:
/// [
///   len: 8 bytes
///   arg0: 16 bytes
///   arg1: 16 bytes
///   ...etc
/// ]
///
/// The compiled rebar instructions will construct a slice with the correct
/// arguments all lined up in memory. Then, that pointer will be passed to rust,
/// where it will be cast to a reference, and then functions like `arg` may be
/// called on it.
///
/// So, TLDR, don't move this thing around. I would wrap it in a `Pin`, but
/// `Pin` is annoying to use, so all the functions are just unsafe instead.
#[repr(C)]
pub struct RebarSlice {
  len:      u64,
  _phantom: PhantomPinned,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct RebarValue {
  pub kind:  u64,
  pub value: i64,
}

impl RebarSlice {
  pub unsafe fn len(&self) -> usize { self.len as usize }

  pub unsafe fn arg(&self, idx: usize) -> RebarValue {
    assert!(idx < self.len as usize);
    unsafe {
      let ptr = self as *const _;
      // `offset(1)` skips the `len` field.
      let arg_ptr = (ptr as *const i64).offset(1) as *const RebarValue;
      *arg_ptr.offset(idx as isize)
    }
  }
}

impl JIT {
  #[allow(clippy::new_without_default)]
  pub fn new(dyn_call_ptr: fn(i64, *const RebarSlice) -> i64) -> Self {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
      panic!("host machine is not supported: {}", msg);
    });
    let isa = isa_builder.finish(settings::Flags::new(flag_builder)).unwrap();
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

    builder.symbol("__call", dyn_call_ptr as *const _);

    let mut module = JITModule::new(builder);

    let mut call_sig = module.make_signature();
    call_sig.params.push(AbiParam::new(ir::types::I64));
    call_sig.params.push(AbiParam::new(ir::types::I64));
    call_sig.returns.push(AbiParam::new(ir::types::I64));

    let call_func = module.declare_function("__call", Linkage::Import, &call_sig).unwrap();

    JIT { data_description: DataDescription::new(), module, call_func }
  }

  pub fn new_thread(&self) -> ThreadCtx {
    let ctx = self.module.make_context();

    ThreadCtx {
      builder_context: FunctionBuilderContext::new(),
      ctx,
      isa: self.module.isa(),
      call_func: self.call_func,
      call_func_decl: self.module.declarations().get_function_decl(self.call_func),
    }
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
    let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
    let entry_block = builder.create_block();

    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Tells the compiler there will be no predecessors (???).
    builder.seal_block(entry_block);

    // TODO: Declare variables.
    // for stmt in source.stmts() {}

    let signature = builder.func.import_signature(self.call_func_decl.signature.clone());
    let user_name_ref = builder.func.declare_imported_user_function(ir::UserExternalName {
      namespace: 0,
      index:     self.call_func.as_u32(),
    });
    let colocated = self.call_func_decl.linkage.is_final();
    let call_func_ref = builder.func.import_function(ir::ExtFuncData {
      name: ir::ExternalName::user(user_name_ref),
      signature,
      colocated,
    });

    FuncBuilder { builder, mir, call_func_ref, locals: HashMap::new(), next_variable: 0 }
  }

  pub fn translate_function(&mut self, mir: &mir::Function) { self.new_function(mir).translate(); }
}

impl FuncBuilder<'_> {
  fn translate(mut self) {
    self.builder.func.signature.returns.push(AbiParam::new(ir::types::I64));

    let return_variable = self.new_variable();
    let zero = self.builder.ins().iconst(ir::types::I64, 0);
    self.builder.def_var(return_variable, zero);

    for &stmt in &self.mir.items {
      let res = self.compile_stmt(stmt);
      self.builder.def_var(return_variable, res);
    }

    let return_value = self.builder.use_var(return_variable);

    // Emit the return instruction.
    self.builder.ins().return_(&[return_value]);

    // Tell the builder we're done with this function.
    self.builder.finalize();
  }
}

impl ThreadCtx<'_> {
  pub fn compile(&mut self) -> &CompiledCode {
    self.ctx.compile(self.isa, &mut ControlPlane::default()).unwrap()
  }

  pub fn func(&self) -> &ir::Function { &self.ctx.func }

  pub fn finalize(mut self, jit: &mut JIT) -> FuncId {
    let id =
      jit.module.declare_function("fooooooo", Linkage::Export, &self.ctx.func.signature).unwrap();
    jit.module.define_function(id, &mut self.ctx).unwrap();
    id
  }

  pub fn clear(&mut self) { self.ctx.clear(); }
}

impl JIT {
  pub fn define_function(
    &mut self,
    code: &[u8],
    alignment: u64,
    func: &ir::Function,
    relocs: &[FinalizedMachReloc],
  ) -> Result<FuncId, String> {
    let id = self.module.declare_function("fooooooo", Linkage::Export, &func.signature).unwrap();
    self
      .module
      .define_function_bytes(id, func, alignment, code, relocs)
      .map_err(|e| e.to_string())?;
    Ok(id)
  }
}

#[derive(Debug)]
pub enum Error {
  MissingExpr,
}

impl FuncBuilder<'_> {
  fn new_variable(&mut self) -> Variable {
    let var = Variable::new(self.next_variable);
    self.builder.declare_var(var, ir::types::I64);
    self.next_variable += 1;
    var
  }

  fn compile_stmt(&mut self, stmt: mir::StmtId) -> Value {
    match self.mir.stmts[stmt] {
      mir::Stmt::Expr(expr) => self.compile_expr(expr),
      mir::Stmt::Let(id, _, expr) => {
        let value = self.compile_expr(expr);
        let variable = self.new_variable();
        self.builder.def_var(variable, value);
        self.locals.insert(id, variable);

        // THis doesn't return a value. TODO: Make `stmt` not return a value.
        self.builder.ins().iconst(ir::types::I64, 0)
      }
    }
  }

  fn compile_expr(&mut self, expr: mir::ExprId) -> Value {
    match self.mir.exprs[expr] {
      mir::Expr::Literal(ref lit) => match lit {
        mir::Literal::Int(i) => self.builder.ins().iconst(ir::types::I64, *i),
        _ => unimplemented!(),
      },

      mir::Expr::Local(id) => self.builder.use_var(self.locals[&id]),

      mir::Expr::Native(ref id, _) => self.builder.ins().iconst(ir::types::I64, id.0 as i64),

      mir::Expr::Block(ref stmts) => {
        // FIXME: Make a new scope so that locals don't leak.
        let mut return_value = self.builder.ins().iconst(ir::types::I64, 0);
        for &stmt in stmts {
          return_value = self.compile_stmt(stmt);
        }
        return_value
      }

      mir::Expr::Call(lhs, ref sig_ty, ref args) => {
        let lhs = self.compile_expr(lhs);

        let slot = self.builder.create_sized_stack_slot(StackSlotData {
          kind: StackSlotKind::ExplicitSlot,
          // Each argument is 16 bytes wide, and we need 8 bytes for the length..
          size: args.len() as u32 * 16 + 8,
        });

        let arg_len = self.builder.ins().iconst(ir::types::I64, args.len() as i64);
        self.builder.ins().stack_store(arg_len, slot, 0);

        let arg_types = match sig_ty {
          Type::Function(ref args, _) => args,
          _ => unreachable!(),
        };

        assert_eq!(args.len(), arg_types.len());

        for (i, (&arg, arg_ty)) in args.iter().zip(arg_types.iter()).enumerate() {
          let arg = self.compile_expr(arg);

          // Each argument is 16 bytes wide, and we need an 8 byte offset for the length.
          // Store the type of the value in the first 8 bytes, and the value itself in the
          // second 8 bytes.
          //
          // TODO: Once unions are supported, this needs to be the runtime type of the
          // value instead of the static type.
          let ty = self.builder.ins().iconst(ir::types::I64, id_of_type(arg_ty));
          self.builder.ins().stack_store(ty, slot, i as i32 * 16 + 8);
          self.builder.ins().stack_store(arg, slot, i as i32 * 16 + 8 + 8);
        }

        let arg_ptr = self.builder.ins().stack_addr(ir::types::I64, slot, 0);

        let call = self.builder.ins().call(self.call_func_ref, &[lhs, arg_ptr]);

        match *sig_ty {
          Type::Function(_, ref ret) => match **ret {
            // TODO: Don't return a value for everything.
            Type::Literal(Literal::Unit) => self.builder.ins().iconst(ir::types::I64, 0),
            _ => self.builder.inst_results(call)[0],
          },
          _ => unreachable!(),
        }
      }

      mir::Expr::Unary(lhs, ref op, _) => {
        let lhs = self.compile_expr(lhs);

        let res = match op {
          mir::UnaryOp::Neg => self.builder.ins().ineg(lhs),
          mir::UnaryOp::Not => self.builder.ins().bxor_imm(lhs, 1),
        };

        #[cfg(debug_assertions)]
        {
          use cranelift::codegen::ir::InstBuilderBase;
          assert_eq!(self.builder.ins().data_flow_graph().value_type(res), ir::types::I64);
        }

        res
      }

      mir::Expr::Binary(lhs, ref op, rhs, _) => {
        let lhs = self.compile_expr(lhs);
        let rhs = self.compile_expr(rhs);

        let res = match op {
          mir::BinaryOp::Add => self.builder.ins().iadd(lhs, rhs),
          mir::BinaryOp::Sub => self.builder.ins().isub(lhs, rhs),
          mir::BinaryOp::Mul => self.builder.ins().imul(lhs, rhs),
          mir::BinaryOp::Div => self.builder.ins().udiv(lhs, rhs),
          mir::BinaryOp::Mod => self.builder.ins().urem(lhs, rhs),

          _ => {
            // `icmp` returns an I8, we want to extend it to an I64. Because we
            // have typechecking, we could probably get away with
            // keeping it as an I8 everywhere, but its a lot simpler
            // to just keep everything an I64.

            let res = match op {
              mir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, lhs, rhs),
              mir::BinaryOp::Neq => self.builder.ins().icmp(IntCC::NotEqual, lhs, rhs),

              // All numbers are signed.
              mir::BinaryOp::Lt => self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs),
              mir::BinaryOp::Lte => self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, lhs, rhs),
              mir::BinaryOp::Gt => self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs),
              mir::BinaryOp::Gte => {
                self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs)
              }

              _ => unreachable!(),
            };

            self.builder.ins().uextend(ir::types::I64, res)
          }
        };

        #[cfg(debug_assertions)]
        {
          use cranelift::codegen::ir::InstBuilderBase;
          assert_eq!(self.builder.ins().data_flow_graph().value_type(res), ir::types::I64);
        }

        res
      }

      mir::Expr::If { cond, then, els: None } => {
        let cond = self.compile_expr(cond);

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

        self.builder.ins().iconst(ir::types::I64, 0)
      }

      mir::Expr::If { cond, then, els: Some(els) } => {
        let cond = self.compile_expr(cond);

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        self.builder.append_block_param(merge_block, ir::types::I64);

        // Test the if condition and conditionally branch.
        self.builder.ins().brif(cond, then_block, &[], else_block, &[]);

        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        let then_return = self.compile_expr(then);

        // Jump to the merge block, passing it the block return value.
        self.builder.ins().jump(merge_block, &[then_return]);

        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        let else_return = self.compile_expr(els);

        // Jump to the merge block, passing it the block return value.
        self.builder.ins().jump(merge_block, &[else_return]);

        // Switch to the merge block for subsequent statements.
        self.builder.switch_to_block(merge_block);

        // We've now seen all the predecessors of the merge block.
        self.builder.seal_block(merge_block);

        // Read the value of the if-else by reading the merge block
        // parameter.
        let phi = self.builder.block_params(merge_block)[0];

        phi
      }

      ref v => unimplemented!("expr: {v:?}"),
    }
  }
}

fn id_of_type(ty: &Type) -> i64 {
  match ty {
    Type::Literal(Literal::Unit) => 0,
    Type::Literal(Literal::Bool) => 1,
    Type::Literal(Literal::Int) => 2,
    _ => unimplemented!(),
  }
}
