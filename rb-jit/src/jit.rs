//! Dead simple JIT implementation. Should only be used for testing.

use codegen::ir;
use core::fmt;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use rb_mir::ast as mir;
use rb_typer::{Literal, Type};

pub struct JIT {
  builder_context:  FunctionBuilderContext,
  ctx:              codegen::Context,
  data_description: DataDescription,
  module:           JITModule,
}

struct BlockBuilder<'a> {
  builder: FunctionBuilder<'a>,
  mir:     &'a mir::Function,
  module:  &'a mut JITModule,
}

pub struct FunctionImpl {
  name: String,
}

#[no_mangle]
extern "C" fn print_impl(num: i64) {
  println!("yoooooo we printin: {:?}", num);
}

impl JIT {
  pub fn new() -> Self {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
      panic!("host machine is not supported: {}", msg);
    });
    let isa = isa_builder.finish(settings::Flags::new(flag_builder)).unwrap();
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

    builder.symbol("print_impl", print_impl as *const u8);

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
      .declare_function(&"fooooooo", Linkage::Export, &self.ctx.func.signature)
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

    BlockBuilder { builder, mir, module: &mut self.module }
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

      mir::Expr::Name(ref name, ref ty) => {
        let sig = self.compile_signature(ty);

        let callee = self
          .module
          .declare_function(&name, Linkage::Import, &sig)
          .expect("problem declaring function");

        let local_callee = self.module.declare_func_in_func(callee, self.builder.func);
        self.builder.ins().func_addr(ir::types::I64, local_callee)
      }

      mir::Expr::Call(lhs, ref sig_ty, ref args) => {
        let lhs = self.compile_expr(lhs);
        let sig = self.compile_signature(sig_ty);

        let mut arg_values = Vec::new();
        for &arg in args {
          arg_values.push(self.compile_expr(arg))
        }

        let sig_ref = self.builder.import_signature(sig);
        let call = self.builder.ins().call_indirect(sig_ref, lhs, &arg_values);

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

  fn compile_signature(&self, ty: &Type) -> Signature {
    let mut sig = self.module.make_signature();

    match ty {
      Type::Function(args, ret) => {
        // Add a parameter for each argument.
        for arg in args {
          let ir_type = match arg {
            Type::Literal(Literal::Int) => ir::types::I64,
            _ => panic!("invalid type: {arg:?}"),
          };

          sig.params.push(AbiParam::new(ir_type));
        }

        match **ret {
          Type::Literal(Literal::Int) => sig.returns.push(AbiParam::new(ir::types::I64)),
          Type::Literal(Literal::Unit) => {}
          _ => panic!("invalid type: {ret:?}"),
        }
      }

      _ => panic!("invalid type: {ty:?}"),
    }

    sig
  }
}
