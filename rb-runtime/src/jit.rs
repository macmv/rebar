//! Dead simple JIT implementation. Should only be used for testing.

use codegen::ir;
use core::fmt;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Linkage, Module};
use rb_syntax::cst;

pub struct JIT {
  builder_context:  FunctionBuilderContext,
  ctx:              codegen::Context,
  data_description: DataDescription,
  module:           JITModule,
}

struct BlockBuilder<'a> {
  builder: FunctionBuilder<'a>,
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
  fn new() -> Self {
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

  fn eval(&mut self) {
    let id = self
      .module
      .declare_function(&"fooooooo", Linkage::Export, &self.ctx.func.signature)
      .map_err(|e| e.to_string())
      .unwrap();
    self.module.define_function(id, &mut self.ctx).map_err(|e| e.to_string()).unwrap();
    self.module.clear_context(&mut self.ctx);
    self.module.finalize_definitions().unwrap();
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

pub fn interpret(source: &cst::SourceFile) -> JIT {
  let mut jit = JIT::new();

  // This is a little cursed, but we'll just dereference the pointer twice. What
  // could possibly go wrong?

  let contents = (print_impl as *const u8 as u64).to_ne_bytes().to_vec();

  jit.data_description.define(contents.into_boxed_slice());
  let id = jit.module.declare_data("my_data", Linkage::Export, true, false).unwrap();

  jit.module.define_data(id, &jit.data_description).unwrap();
  jit.data_description.clear();
  jit.module.finalize_definitions().unwrap();

  // let mut sig = Signature::new(isa::CallConv::SystemV);
  // sig.params.push(AbiParam::new(ir::types::I64));

  // jit
  //   .module
  //   .declare_function("print_impl", Linkage::Import, &sig)
  //   .map_err(|e| e.to_string())
  //   .unwrap();
  // jit.module.finalize_definitions().unwrap();

  jit.ctx.func.signature.returns.push(AbiParam::new(ir::types::I64));

  let mut block = jit.new_block(source);

  let return_variable = Variable::new(0);
  block.builder.declare_var(return_variable, ir::types::I64);
  let zero = block.builder.ins().iconst(ir::types::I64, 0);
  block.builder.def_var(return_variable, zero);

  for stmt in source.stmts() {
    let res = block.compile_stmt(&stmt);
    block.builder.def_var(return_variable, res);
  }

  let return_value = block.builder.use_var(return_variable);

  // Emit the return instruction.
  block.builder.ins().return_(&[return_value]);

  // Tell the builder we're done with this function.
  block.builder.finalize();

  jit.eval();

  jit
}

#[derive(Debug)]
pub enum Error {
  MissingExpr,
}

impl JIT {
  fn new_block<'a>(&'a mut self, _source: &cst::SourceFile) -> BlockBuilder<'a> {
    let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
    let entry_block = builder.create_block();

    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Tells the compiler there will be no predecessors (???).
    builder.seal_block(entry_block);

    // TODO: Declare variables.
    // for stmt in source.stmts() {}

    BlockBuilder { builder, module: &mut self.module }
  }
}

impl BlockBuilder<'_> {
  fn compile_stmt(&mut self, stmt: &cst::Stmt) -> Value {
    match stmt {
      cst::Stmt::ExprStmt(expr) => self.compile_expr(&expr.expr().unwrap()),
      _ => unimplemented!(),
    }
  }

  fn compile_expr(&mut self, expr: &cst::Expr) -> Value {
    match expr {
      cst::Expr::Literal(lit) => {
        if let Some(lit) = lit.integer_token() {
          self.builder.ins().iconst(ir::types::I64, lit.text().parse::<i64>().unwrap())
        } else {
          unimplemented!()
        }
      }
      cst::Expr::Name(name) => {
        let ident = name.ident_token().unwrap();
        let _name = ident.text();

        // TODO
        // self
        //   .variables
        //   .iter()
        //   .find(|(n, _)| n == &name)
        //   .map(|(_, v)| v.clone())
        //   .unwrap_or_else(|| Value::Function(Arc::new(FunctionImpl { name:
        // name.to_string() })))

        todo!()
      }
      cst::Expr::CallExpr(bin) => {
        let lhs = bin.expr().unwrap();
        let args = bin.arg_list().unwrap();

        let name = match lhs {
          cst::Expr::Name(name) => {
            let ident = name.ident_token().unwrap();
            ident.text().to_string()
          }
          _ => todo!(),
        };

        let mut sig = self.module.make_signature();

        // Add a parameter for each argument.
        for _arg in args.exprs() {
          sig.params.push(AbiParam::new(ir::types::I64));
        }

        // For simplicity for now, just make all calls return a single I64.
        // sig.returns.push(AbiParam::new(self.int));

        // TODO: Streamline the API here?
        // let callee = self
        //   .module
        //   .declare_function(&name, Linkage::Import, &sig)
        //   .expect("problem declaring function");

        let callee = self
          .module
          .declare_function(&name, Linkage::Import, &sig)
          .expect("problem declaring function");

        let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

        let mut arg_values = Vec::new();
        for arg in args.exprs() {
          arg_values.push(self.compile_expr(&arg))
        }
        let call = self.builder.ins().call(local_callee, &arg_values);
        self.builder.inst_results(call);

        self.builder.ins().iconst(ir::types::I64, 0)
      }
      cst::Expr::BinaryExpr(bin) => {
        let lhs = bin.lhs().unwrap();
        let rhs = bin.rhs().unwrap();
        let op = bin.binary_op().unwrap();

        let lhs = self.compile_expr(&lhs);
        let rhs = self.compile_expr(&rhs);

        if op.plus_token().is_some() {
          // TODO: Get static types in here! For now, assume everything is an int.

          self.builder.ins().iadd(lhs, rhs)
        } else if op.star_token().is_some() {
          self.builder.ins().imul(lhs, rhs)
        } else {
          unimplemented!()
        }
      }
      _ => unimplemented!("expr: {expr:?}"),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn interp(source: &str) { interpret(&cst::SourceFile::parse(source).tree()); }

  #[test]
  fn foo() {
    interp(
      r#"print_impl(2 * 3 + 4)
         4
      "#,
    );

    panic!();
  }
}
