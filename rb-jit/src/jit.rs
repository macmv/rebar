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
use std::{collections::HashMap, fmt::write, marker::PhantomPinned};

use crate::value::{CompactValues, ParamSize, RValue};

pub struct JIT {
  module: JITModule,

  // TODO: Use this for string literals at the very least.
  #[allow(dead_code)]
  data_description: DataDescription,

  funcs: NativeFuncs<FuncId>,
}

pub struct ThreadCtx<'a> {
  builder_context: FunctionBuilderContext,
  ctx:             codegen::Context,

  isa: &'a dyn TargetIsa,

  funcs: NativeFuncs<NativeFuncDecl<'a>>,
}

#[derive(Clone, Copy)]
struct NativeFuncDecl<'a> {
  id:   FuncId,
  decl: &'a FunctionDeclaration,
}

struct NativeFuncs<T> {
  call: T,
}

impl<T: Copy> NativeFuncs<T> {
  fn map<U>(&self, mut f: impl FnMut(T) -> U) -> NativeFuncs<U> {
    NativeFuncs { call: f(self.call) }
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
  locals:        HashMap<mir::VarId, CompactValues<Variable>>,
  next_variable: usize,
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
pub struct RebarSlice {
  _phantom: PhantomPinned,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union RebarValue {
  pub nil: (),
  pub one: i64,
  pub two: [i64; 2],
}

impl RebarSlice {
  pub unsafe fn arg(&self, offset: usize) -> *const RebarValue {
    unsafe {
      let ptr = self as *const _;
      (ptr as *const i64).offset(offset as isize) as *const RebarValue
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

    JIT { data_description: DataDescription::new(), module, funcs: NativeFuncs { call: call_func } }
  }

  pub fn new_thread(&self) -> ThreadCtx {
    let ctx = self.module.make_context();

    ThreadCtx {
      builder_context: FunctionBuilderContext::new(),
      ctx,
      isa: self.module.isa(),

      funcs: self.funcs(),
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
    let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
    let entry_block = builder.create_block();

    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Tells the compiler there will be no predecessors (???).
    builder.seal_block(entry_block);

    // TODO: Declare variables.
    // for stmt in source.stmts() {}

    let funcs = self.funcs.map(|func| {
      let signature = builder.func.import_signature(func.decl.signature.clone());
      let user_name_ref = builder.func.declare_imported_user_function(ir::UserExternalName {
        namespace: 0,
        index:     func.id.as_u32(),
      });
      let colocated = func.decl.linkage.is_final();
      builder.func.import_function(ir::ExtFuncData {
        name: ir::ExternalName::user(user_name_ref),
        signature,
        colocated,
      })
    });

    FuncBuilder { builder, mir, funcs, locals: HashMap::new(), next_variable: 0 }
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
      // self.def_var(return_variable, res.to_ir());
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

  fn def_var(&mut self, var: CompactValues<Variable>, ir: CompactValues<ir::Value>) {
    match (var, ir) {
      (CompactValues::None, CompactValues::None) => {}
      (CompactValues::None, _) => panic!("cannot assign a value to a nil"),

      // This is effectively setting a value to `nil`. Shouldn't ever happen.
      (CompactValues::One(_), CompactValues::None) => panic!("cannot assign nil to a variable"),
      (CompactValues::One(var), CompactValues::One(value)) => {
        self.builder.def_var(var, value);
      }
      // This is effectively assigning a union to a single variable. Definition doesn't make sense.
      (CompactValues::One(_), CompactValues::Two(_, _)) => {
        panic!("cannot assign a union to a variable")
      }

      // Any value can be assigned to a union.
      (CompactValues::Two(var0, var1), _) => {
        // The `ir` must be in extended form, which means it must have a length of 1 or
        // 2.
        assert!(ir.len() == 1 || ir.len() == 2);

        // The first value is the only one that must be set. For example, if a value is
        // set to `nil`, the second variable is undefined.
        ir.with_slice(|slice| {
          for (var, &value) in [var0, var1].into_iter().zip(slice.iter()) {
            self.builder.def_var(var, value);
          }
        });
      }
    }
  }

  fn use_var(&mut self, var: CompactValues<Variable>) -> RValue {
    match var {
      CompactValues::None => RValue::Nil,
      CompactValues::One(var) => {
        let ir = self.builder.use_var(var);
        // TODO: Need to get the static type in here and use that.
        RValue::Int(ir)
      }
      CompactValues::Two(ty, value) => {
        let _ty = self.builder.use_var(ty);
        let value = self.builder.use_var(value);

        // TODO: RValue from type.
        RValue::Int(value)
      }
    }
  }

  fn compile_stmt(&mut self, stmt: mir::StmtId) -> RValue {
    match self.mir.stmts[stmt] {
      mir::Stmt::Expr(expr) => self.compile_expr(expr),
      mir::Stmt::Let(id, ref ty, expr) => {
        let value = self.compile_expr(expr);
        let ir = value.to_sized_ir(param_size_of_type(&ty), &mut self.builder);

        let variables = ir.map(|_| self.new_variable());

        self.def_var(variables, ir);
        self.locals.insert(id, variables);

        RValue::Nil
      }
    }
  }

  fn compile_expr(&mut self, expr: mir::ExprId) -> RValue {
    match self.mir.exprs[expr] {
      mir::Expr::Literal(ref lit) => match lit {
        mir::Literal::Nil => RValue::Nil,
        mir::Literal::Bool(v) => {
          RValue::Bool(self.builder.ins().iconst(ir::types::I8, if *v { 1 } else { 0 }))
        }
        mir::Literal::Int(i) => RValue::Int(self.builder.ins().iconst(ir::types::I64, *i)),
      },

      mir::Expr::Local(id) => self.use_var(self.locals[&id]),

      mir::Expr::Native(ref id, _) => {
        RValue::Function(self.builder.ins().iconst(ir::types::I64, id.0 as i64))
      }

      mir::Expr::Block(ref stmts) => {
        // FIXME: Make a new scope so that locals don't leak.
        let mut return_value = RValue::Nil;
        for &stmt in stmts {
          return_value = self.compile_stmt(stmt);
        }
        return_value
      }

      mir::Expr::Call(lhs, ref sig_ty, ref args) => {
        let lhs = self.compile_expr(lhs);

        let arg_types = match sig_ty {
          Type::Function(ref args, _) => args,
          _ => unreachable!(),
        };

        assert_eq!(args.len(), arg_types.len());

        // Argument length in 8 byte increments.
        let mut arg_len = 0;
        for arg_ty in arg_types.iter() {
          arg_len += param_size_of_type(arg_ty).len();
        }

        let slot = self.builder.create_sized_stack_slot(StackSlotData {
          kind: StackSlotKind::ExplicitSlot,
          // Each argument is 8 bytes wide.
          size: arg_len * 8,
        });

        let mut slot_index = 0;
        for (&arg, arg_ty) in args.iter().zip(arg_types.iter()) {
          let arg = self.compile_expr(arg);

          let v = arg.to_sized_ir(param_size_of_type(arg_ty), &mut self.builder);

          v.with_slice(|slice| {
            for &v in slice.iter() {
              self.builder.ins().stack_store(v, slot, slot_index * 8);
              slot_index += 1;
            }
          });
        }

        let arg_ptr = self.builder.ins().stack_addr(ir::types::I64, slot, 0);

        let func = lhs.as_function().unwrap();
        let call = self.builder.ins().call(self.funcs.call, &[func, arg_ptr]);

        match *sig_ty {
          Type::Function(_, ref ret) => match **ret {
            // FIXME: Need to create RValues from ir extended form.
            Type::Literal(Literal::Unit) => RValue::Nil,
            _ => RValue::Int(self.builder.inst_results(call)[0]),
          },
          _ => unreachable!(),
        }
      }

      mir::Expr::Unary(lhs, ref op, _) => {
        let lhs = self.compile_expr(lhs);

        let res = match op {
          mir::UnaryOp::Neg => RValue::Int(self.builder.ins().ineg(lhs.as_int().unwrap())),
          mir::UnaryOp::Not => RValue::Bool(self.builder.ins().bxor_imm(lhs.as_bool().unwrap(), 1)),
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
            let lhs = lhs.as_int().unwrap();
            let rhs = rhs.as_int().unwrap();

            let res = match op {
              mir::BinaryOp::Add => self.builder.ins().iadd(lhs, rhs),
              mir::BinaryOp::Sub => self.builder.ins().isub(lhs, rhs),
              mir::BinaryOp::Mul => self.builder.ins().imul(lhs, rhs),
              mir::BinaryOp::Div => self.builder.ins().udiv(lhs, rhs),
              mir::BinaryOp::Mod => self.builder.ins().urem(lhs, rhs),
              _ => unreachable!(),
            };

            RValue::Int(res)
          }

          mir::BinaryOp::Eq | mir::BinaryOp::Neq => match (lhs, rhs) {
            (RValue::Nil, RValue::Nil) => {
              let tru = self.builder.ins().iconst(ir::types::I8, 1);
              RValue::Bool(tru)
            }
            (RValue::Bool(l), RValue::Bool(r)) => {
              let res = match op {
                mir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, l, r),
                mir::BinaryOp::Neq => self.builder.ins().icmp(IntCC::NotEqual, l, r),
                _ => unreachable!(),
              };

              RValue::Bool(res)
            }
            (RValue::Int(l), RValue::Int(r)) => {
              let res = match op {
                mir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, l, r),
                mir::BinaryOp::Neq => self.builder.ins().icmp(IntCC::NotEqual, l, r),
                _ => unreachable!(),
              };

              RValue::Bool(res)
            }

            (RValue::Dynamic(lty, l), RValue::Dynamic(rty, r)) => {
              let res = match op {
                mir::BinaryOp::Eq => {
                  let ty_eq = self.builder.ins().icmp(IntCC::Equal, lty, rty);
                  let v_eq = self.builder.ins().icmp(IntCC::Equal, l, r);
                  self.builder.ins().band(ty_eq, v_eq)
                }
                mir::BinaryOp::Neq => {
                  let ty_neq = self.builder.ins().icmp(IntCC::NotEqual, l, r);
                  let v_neq = self.builder.ins().icmp(IntCC::NotEqual, l, r);

                  self.builder.ins().bor(ty_neq, v_neq)
                }
                _ => unreachable!(),
              };

              RValue::Bool(res)
            }

            (RValue::Dynamic(lty, l), _) => {
              let rhs = rhs.to_sized_ir(ParamSize::Double, &mut self.builder);

              let res = match op {
                mir::BinaryOp::Eq => match rhs {
                  CompactValues::None => unreachable!(),
                  CompactValues::One(rty) => self.builder.ins().icmp(IntCC::Equal, lty, rty),
                  CompactValues::Two(rty, r) => {
                    let ty_eq = self.builder.ins().icmp(IntCC::Equal, lty, rty);
                    let v_eq = self.builder.ins().icmp(IntCC::Equal, l, r);
                    self.builder.ins().band(ty_eq, v_eq)
                  }
                },
                mir::BinaryOp::Neq => match rhs {
                  CompactValues::None => unreachable!(),
                  CompactValues::One(rty) => self.builder.ins().icmp(IntCC::NotEqual, lty, rty),
                  CompactValues::Two(rty, r) => {
                    let ty_eq = self.builder.ins().icmp(IntCC::NotEqual, lty, rty);
                    let v_eq = self.builder.ins().icmp(IntCC::NotEqual, l, r);
                    self.builder.ins().bor(ty_eq, v_eq)
                  }
                },
                _ => unreachable!(),
              };

              RValue::Bool(res)
            }

            (l, r) => unreachable!("cannot compare values {l:?} and {r:?}"),
          },

          _ => {
            let lhs = lhs.as_int().unwrap();
            let rhs = rhs.as_int().unwrap();

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

            RValue::Bool(res)
          }
        };

        res
      }

      mir::Expr::If { cond, then, els: None, ty: _ } => {
        let cond = self.compile_expr(cond);
        let cond = cond.as_bool().unwrap();

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

        RValue::Nil
      }

      mir::Expr::If { cond, then, els: Some(els), ref ty } => {
        let cond = self.compile_expr(cond);
        let cond = cond.as_bool().unwrap();

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        let param_size = param_size_of_type(&ty);

        // FIXME: Get the static types in here and append the parameters we need.
        param_size.append_block_params(&mut self.builder, merge_block);

        // Test the if condition and conditionally branch.
        self.builder.ins().brif(cond, then_block, &[], else_block, &[]);

        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        let then_return = self.compile_expr(then).to_sized_ir(param_size, &mut self.builder);

        // Jump to the merge block, passing it the block return value.
        then_return.with_slice(|slice| {
          self.builder.ins().jump(merge_block, slice);
        });

        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        let else_return = self.compile_expr(els).to_sized_ir(param_size, &mut self.builder);

        // Jump to the merge block, passing it the block return value.
        else_return.with_slice(|slice| {
          self.builder.ins().jump(merge_block, slice);
        });

        // Switch to the merge block for subsequent statements.
        self.builder.switch_to_block(merge_block);

        // We've now seen all the predecessors of the merge block.
        self.builder.seal_block(merge_block);

        // Read the value of the if-else by reading the merge block
        // parameter.
        RValue::from_sized_ir(self.builder.block_params(merge_block), ty)
      }

      ref v => unimplemented!("expr: {v:?}"),
    }
  }
}

fn param_size_of_type(ty: &Type) -> ParamSize {
  match ty {
    Type::Literal(Literal::Unit) => ParamSize::Unit,
    Type::Union(_) => ParamSize::Double,
    _ => ParamSize::Single,
  }
}
