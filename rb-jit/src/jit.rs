use codegen::ir::{self, FuncRef};
use core::fmt;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use rb_mir::ast as mir;
use rb_typer::{Literal, Type};
use std::marker::PhantomPinned;

pub struct JIT {
  builder_context: FunctionBuilderContext,
  ctx:             codegen::Context,

  module: JITModule,

  // TODO: Use this for string literals at the very least.
  #[allow(dead_code)]
  data_description: DataDescription,
}

struct BlockBuilder<'a> {
  builder:       FunctionBuilder<'a>,
  mir:           &'a mir::Function,
  call_func_ref: FuncRef,

  // I think I'll need this? Not entirely sure.
  #[allow(dead_code)]
  module: &'a JITModule,
}

pub struct FunctionImpl {
  name: String,
}

/// This struct is horribly dangerous to use.
///
/// It should only be constructed from within the rebar runtime. The layout
/// should look something like this:
/// [
///   len: 8 bytes
///   arg0: 8 bytes
///   arg1: 8 bytes
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

impl RebarSlice {
  pub unsafe fn len(&self) -> usize { self.len as usize }

  pub unsafe fn arg(&self, idx: usize) -> i64 {
    assert!(idx < self.len as usize);
    unsafe {
      let ptr = self as *const _;
      let arg_ptr = (ptr as *const i64).offset(1);
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

    let module = JITModule::new(builder);
    JIT {
      builder_context: FunctionBuilderContext::new(),
      ctx: module.make_context(),
      data_description: DataDescription::new(),
      module,
    }
  }

  pub fn compile_function(&mut self, mir: &mir::Function) -> FuncId {
    self.ctx.func.signature.returns.push(AbiParam::new(ir::types::I64));

    let mut block = self.new_block(mir);

    let return_variable = Variable::new(0);
    block.builder.declare_var(return_variable, ir::types::I64);
    let zero = block.builder.ins().iconst(ir::types::I64, 0);
    block.builder.def_var(return_variable, zero);

    for &stmt in &mir.items {
      let res = block.compile_stmt(stmt);
      block.builder.def_var(return_variable, res);
    }

    let return_value = block.builder.use_var(return_variable);

    // Emit the return instruction.
    block.builder.ins().return_(&[return_value]);

    // Tell the builder we're done with this function.
    block.builder.finalize();

    let id = self
      .module
      .declare_function("fooooooo", Linkage::Export, &self.ctx.func.signature)
      .map_err(|e| e.to_string())
      .unwrap();
    self.module.define_function(id, &mut self.ctx).map_err(|e| e.to_string()).unwrap();
    self.module.clear_context(&mut self.ctx);
    id
  }

  pub fn finalize(&mut self) { self.module.finalize_definitions().unwrap(); }

  pub fn eval(&mut self, id: FuncId) {
    let code = self.module.get_finalized_function(id);

    unsafe {
      let code: fn() -> i64 = std::mem::transmute(code);
      println!("Result: {}", code());
    }
  }
}

impl fmt::Debug for FunctionImpl {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "FunctionImpl({})", self.name)
  }
}

impl FunctionImpl {
  pub fn call(&self, args: Vec<Value>) -> Value {
    println!("calling {} with args {:?}", self.name, args);

    todo!()
  }
}

#[derive(Debug)]
pub enum Error {
  MissingExpr,
}

impl JIT {
  fn new_block<'a>(&'a mut self, mir: &'a mir::Function) -> BlockBuilder<'a> {
    let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
    let entry_block = builder.create_block();

    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Tells the compiler there will be no predecessors (???).
    builder.seal_block(entry_block);

    // TODO: Declare variables.
    // for stmt in source.stmts() {}

    let mut call_sig = self.module.make_signature();
    call_sig.params.push(AbiParam::new(ir::types::I64));
    call_sig.params.push(AbiParam::new(ir::types::I64));
    call_sig.returns.push(AbiParam::new(ir::types::I64));

    let callee = self.module.declare_function("__call", Linkage::Import, &call_sig).unwrap();

    let call_func_ref = self.module.declare_func_in_func(callee, builder.func);

    BlockBuilder { builder, mir, module: &mut self.module, call_func_ref }
  }
}

impl BlockBuilder<'_> {
  fn compile_stmt(&mut self, stmt: mir::StmtId) -> Value {
    match self.mir.stmts[stmt] {
      mir::Stmt::Expr(expr) => self.compile_expr(expr),
    }
  }

  fn compile_expr(&mut self, expr: mir::ExprId) -> Value {
    match self.mir.exprs[expr] {
      mir::Expr::Literal(ref lit) => match lit {
        mir::Literal::Int(i) => self.builder.ins().iconst(ir::types::I64, *i),
        _ => unimplemented!(),
      },

      mir::Expr::Name(ref name, ref _ty) => {
        let id = match name.as_str() {
          "assert_eq" => 0,
          "println" => 1,
          _ => panic!("unknown name {name}"),
        };

        self.builder.ins().iconst(ir::types::I64, id)
      }

      mir::Expr::Call(lhs, ref sig_ty, ref args) => {
        let lhs = self.compile_expr(lhs);

        // Store 2 values:
        // - The length of the arguments.
        // - The first argument.
        let slot = self.builder.create_sized_stack_slot(StackSlotData {
          kind: StackSlotKind::ExplicitSlot,
          // Each argument is 8 bytes wide.
          size: (args.len() as u32 + 1) * 8,
        });

        let arg_len = self.builder.ins().iconst(ir::types::I64, args.len() as i64);
        self.builder.ins().stack_store(arg_len, slot, 0);

        for (i, &arg) in args.iter().enumerate() {
          let arg = self.compile_expr(arg);

          // Each argument is 8 bytes wide.
          self.builder.ins().stack_store(arg, slot, (i as i32 + 1) * 8);
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

      mir::Expr::Binary(lhs, ref op, rhs, ref result) => {
        let lhs = self.compile_expr(lhs);
        let rhs = self.compile_expr(rhs);

        match (op, result) {
          (mir::BinaryOp::Add, _) => self.builder.ins().iadd(lhs, rhs),
          (mir::BinaryOp::Sub, _) => self.builder.ins().isub(lhs, rhs),
          (mir::BinaryOp::Mul, _) => self.builder.ins().imul(lhs, rhs),
          (mir::BinaryOp::Div, _) => self.builder.ins().udiv(lhs, rhs),
          (mir::BinaryOp::Mod, _) => self.builder.ins().urem(lhs, rhs),
          _ => unimplemented!(),
        }
      }
      _ => unimplemented!("expr: {expr:?}"),
    }
  }
}
