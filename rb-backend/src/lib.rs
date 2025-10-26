use std::collections::HashMap;

use rb_codegen::{
  Condition, Function, FunctionBuilder, FunctionId, InstructionInput, Math, Signature,
  TerminatorInstruction, Variable, VariableSize::*,
};
use rb_mir::{ast as mir, MirContext};

mod r_value;
// mod slot;

use rb_typer::Type;
use rb_value::ValueType;

use crate::r_value::RValue;

pub struct Compiler {
  mir_ctx:      MirContext,
  function_ids: HashMap<mir::UserFunctionId, FunctionId>,

  functions: Vec<Function>,
}

#[derive(Clone, Copy)]
pub struct ThreadCtx<'a> {
  mir_ctx:      &'a MirContext,
  function_ids: &'a HashMap<mir::UserFunctionId, FunctionId>,
}

pub struct FuncBuilder<'a> {
  ctx: ThreadCtx<'a>,

  builder: FunctionBuilder,
  mir:     &'a mir::Function,

  locals: HashMap<mir::VarId, RValue>,
}

impl Compiler {
  pub fn new(mir_ctx: MirContext) -> Self {
    Compiler { mir_ctx, function_ids: HashMap::new(), functions: vec![] }
  }

  pub fn new_thread(&self) -> ThreadCtx<'_> {
    ThreadCtx { mir_ctx: &self.mir_ctx, function_ids: &self.function_ids }
  }

  pub fn declare_function(&mut self, mir: &mir::Function) {
    let mut args = vec![];

    for arg in mir.params.iter() {
      let dvt = ValueType::for_type(&self.mir_ctx, &arg);
      for _ in 0..dvt.len(&self.mir_ctx) {
        args.push(Bit64);
      }
    }

    // TODO: I think the compiler needs the signature?
    let _sig = Signature { args, rets: vec![] };
    let func_id = FunctionId::new(self.function_ids.len() as u32);
    self.function_ids.insert(mir.id, func_id);
  }

  pub fn finish_function(&mut self, func: Function) { self.functions.push(func); }

  pub fn finish(self, start: mir::UserFunctionId) {
    let mut builder = rb_codegen_x86::ObjectBuilder::default();
    for function in self.functions {
      builder.add_function(function);
    }
    builder.set_start_function(self.function_ids[&start]);
    let object = builder.finish();
    object.save(std::path::Path::new("out.o"));

    let status = std::process::Command::new("wild").arg("out.o").status().unwrap();
    if !status.success() {
      panic!("linker failed");
    }
  }
}

impl ThreadCtx<'_> {
  fn new_function<'a>(&'a mut self, mir: &'a mir::Function) -> FuncBuilder<'a> {
    let mut args = vec![];

    for arg in mir.params.iter() {
      let dvt = ValueType::for_type(self.mir_ctx, &arg);
      for _ in 0..dvt.len(self.mir_ctx) {
        args.push(Bit64);
      }
    }

    let builder = FunctionBuilder::new(Signature { args, rets: vec![] });
    let mut locals = HashMap::new();

    let mut i = 0;
    for (var, arg) in mir.params.iter().enumerate() {
      let vt = ValueType::for_type(self.mir_ctx, &arg);
      let mut values = vec![];
      for _ in 0..vt.len(self.mir_ctx) {
        values.push(builder.arg(i));
        i += 1;
      }
      locals.insert(mir::VarId(var as u32), RValue::new(vt, values));
    }

    FuncBuilder { ctx: *self, mir, builder, locals }
  }

  pub fn compile_function(&mut self, mir: &mir::Function) -> Function {
    let mut function = self.new_function(mir).translate();
    rb_codegen_opt::optimize(&mut function);
    function
  }
}

impl FuncBuilder<'_> {
  fn translate(mut self) -> Function {
    let mut res = None;
    for &stmt in &self.mir.items {
      res = Some(self.compile_stmt(stmt));
    }

    if let Some(res) = res {
      let ir = res.to_ir(&mut self);
      self
        .builder
        .current_block()
        .terminate(TerminatorInstruction::Return(ir.into_iter().map(|v| v.into()).collect()));
    }

    self.builder.build()
  }
}

#[derive(Debug)]
pub enum Error {
  MissingExpr,
}

impl FuncBuilder<'_> {
  const fn mir(&self) -> &MirContext { self.ctx.mir_ctx }

  fn compile_stmt(&mut self, stmt: mir::StmtId) -> RValue {
    match self.mir.stmts[stmt] {
      mir::Stmt::Expr(expr) => self.compile_expr(expr),
      mir::Stmt::Let(id, ref _ty, expr) => {
        let value = self.compile_expr(expr);
        self.locals.insert(id, value);

        RValue::nil()
      }
    }
  }

  fn compile_expr(&mut self, expr: mir::ExprId) -> RValue {
    match self.mir.exprs[expr] {
      mir::Expr::Literal(ref lit) => match lit {
        mir::Literal::Nil => RValue::nil(),
        mir::Literal::Bool(v) => RValue::bool(self.builder.instr().mov(Bit1, *v as u64)),
        mir::Literal::Int(i) => RValue::int(self.builder.instr().mov(Bit64, *i as u64)),
        mir::Literal::String(s) => {
          let symbol = self.builder.add_data(s.as_bytes());
          let addr = self.builder.instr().lea(symbol, Bit64);
          RValue::string(addr, self.builder.instr().mov(Bit64, s.len() as u64))
        }
      },

      mir::Expr::Array(_, _) => todo!("array literals"),

      mir::Expr::Local(id, _) => self.locals[&id].clone(),

      mir::Expr::UserFunction(id, _) => RValue::const_user_function(id.0),

      mir::Expr::Native(ref id, _) => RValue::function(self.builder.instr().mov(Bit64, id.0)),

      mir::Expr::Block(ref stmts) => {
        let mut return_value = RValue::nil();

        for &stmt in stmts {
          return_value = self.compile_stmt(stmt);
        }

        return_value
      }

      mir::Expr::Call(function, ref sig_ty, ref args) => {
        let arg_types = match sig_ty {
          Type::Function(ref args, _) => args,
          _ => unreachable!(),
        };

        // Argument length in 8 byte increments.
        let mut arg_values = vec![];
        for (&arg, _arg_ty) in args.iter().zip(arg_types.iter()) {
          let arg = self.compile_expr(arg);

          let v = arg.to_ir(self);
          arg_values.extend(v.into_iter().map(|v| InstructionInput::from(v)));
        }

        let _ret_ty = match *sig_ty {
          Type::Function(_, ref ret) => ret,
          _ => unreachable!(),
        };

        let output = self.builder.instr().call(self.ctx.function_ids[&function], &arg_values);
        RValue::int(output)
      }

      mir::Expr::CallIntrinsic(mir::Intrinsic::Syscall, ref args) => {
        let output = match args.as_slice() {
          &[a1] => {
            let a1 = self.compile_expr(a1).unwrap_single(self);

            self.builder.instr().syscall1(Bit64, a1)
          }
          &[a1, a2] => {
            let a1 = self.compile_expr(a1).unwrap_single(self);
            let a2 = self.compile_expr(a2).unwrap_single(self);

            self.builder.instr().syscall2(Bit64, a1, a2)
          }
          &[a1, a2, a3] => {
            let a1 = self.compile_expr(a1).unwrap_single(self);
            let a2 = self.compile_expr(a2).unwrap_single(self);
            let a3 = self.compile_expr(a3).unwrap_single(self);

            self.builder.instr().syscall3(Bit64, a1, a2, a3)
          }
          &[a1, a2, a3, a4] => {
            let a1 = self.compile_expr(a1).unwrap_single(self);
            let a2 = self.compile_expr(a2).unwrap_single(self);
            let a3 = self.compile_expr(a3).unwrap_single(self);
            let a4 = self.compile_expr(a4).unwrap_single(self);

            self.builder.instr().syscall4(Bit64, a1, a2, a3, a4)
          }
          _ => unreachable!(),
        };

        RValue::int(output)
      }

      mir::Expr::CallIntrinsic(mir::Intrinsic::StringPtr, ref args) => {
        match self.compile_expr(args[0]).kind {
          r_value::RValueKind::Dyn(ref v) => RValue::int(v[0]),
          _ => unreachable!(),
        }
      }

      mir::Expr::CallIntrinsic(mir::Intrinsic::StringLen, ref args) => {
        match self.compile_expr(args[0]).kind {
          r_value::RValueKind::Dyn(ref v) => RValue::int(v[1]),
          _ => unreachable!(),
        }
      }

      mir::Expr::CallIntrinsic(mir::Intrinsic::Trap, _) => {
        self.builder.current_block().terminate(TerminatorInstruction::Trap);
        RValue::nil()
      }

      /*
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
            Slot::Single(v) => match v.size() {
              Bit64 => arg_values.push(v),
              _ => todo!(),
            },
            Slot::Multiple(len, slot) => {
              todo!();
              // for i in 0..len {
              //   arg_values.push(self.builder.instr().stack_load(
              //     VariableSize::Bit64,
              //     slot.clone(),
              //     i as i32 * 8,
              //   ));
              // }
            }
          }
        }

        let func_ref = self.user_funcs[&id];
        let call = self.builder.instr().call(func_ref, Bit64, &arg_values);

        match *sig_ty {
          Type::Function(_, ref ret) => match **ret {
            // FIXME: Need to create RValues from ir extended form.
            Type::Literal(Literal::Unit) => RValue::nil(),
            _ => RValue::int(self.builder.inst_results(call)[0]),
          },
          _ => unreachable!(),
        }
      }
      */
      mir::Expr::Unary(lhs, ref op, _) => {
        let lhs = self.compile_expr(lhs);
        let lhs = lhs.unwrap_single(self);

        let res = match op {
          mir::UnaryOp::Neg => RValue::int(self.builder.instr().math1(Math::Neg, Bit64, lhs)),
          mir::UnaryOp::Not => RValue::bool(self.builder.instr().math2(Math::Xor, Bit1, lhs, 1)),
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
          | mir::BinaryOp::Mod
          | mir::BinaryOp::BitOr
          | mir::BinaryOp::BitAnd
          | mir::BinaryOp::Xor
          | mir::BinaryOp::ShiftLeft
          | mir::BinaryOp::ShiftRight => {
            let lhs = lhs.unwrap_single(self);
            let rhs = rhs.unwrap_single(self);

            let math = match op {
              mir::BinaryOp::Add => rb_codegen::Math::Add,
              mir::BinaryOp::Sub => rb_codegen::Math::Sub,
              mir::BinaryOp::Mul => rb_codegen::Math::Imul,
              mir::BinaryOp::Div => rb_codegen::Math::Idiv,
              mir::BinaryOp::Mod => rb_codegen::Math::Urem,
              mir::BinaryOp::BitOr => rb_codegen::Math::Or,
              mir::BinaryOp::BitAnd => rb_codegen::Math::And,
              mir::BinaryOp::Xor => rb_codegen::Math::Xor,
              mir::BinaryOp::ShiftLeft => rb_codegen::Math::Shl,
              mir::BinaryOp::ShiftRight => rb_codegen::Math::Ishr,
              _ => unreachable!(),
            };

            RValue::int(self.builder.instr().math2(math, Bit64, lhs, rhs))
          }

          mir::BinaryOp::Eq | mir::BinaryOp::Neq => match (lhs.const_ty(), rhs.const_ty()) {
            (Some(ValueType::Nil), Some(ValueType::Nil)) => {
              RValue::bool(self.builder.instr().mov(Bit1, 1))
            }
            (Some(ValueType::Bool), Some(ValueType::Bool)) => {
              let l = lhs.unwrap_single(self);
              let r = rhs.unwrap_single(self);

              let res = match op {
                mir::BinaryOp::Eq => self.builder.instr().cmp(Condition::Equal, Bit1, l, r),
                mir::BinaryOp::Neq => self.builder.instr().cmp(Condition::NotEqual, Bit1, l, r),
                _ => unreachable!(),
              };

              RValue::bool(res)
            }
            (Some(ValueType::Int), Some(ValueType::Int)) => {
              let l = lhs.unwrap_single(self);
              let r = rhs.unwrap_single(self);

              let res = match op {
                mir::BinaryOp::Eq => self.builder.instr().cmp(Condition::Equal, Bit1, l, r),
                mir::BinaryOp::Neq => self.builder.instr().cmp(Condition::NotEqual, Bit1, l, r),
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
              mir::BinaryOp::Lt => self.builder.instr().cmp(Condition::Less, Bit1, lhs, rhs),
              mir::BinaryOp::Lte => self.builder.instr().cmp(Condition::LessEqual, Bit1, lhs, rhs),
              mir::BinaryOp::Gt => self.builder.instr().cmp(Condition::Greater, Bit1, lhs, rhs),
              mir::BinaryOp::Gte => {
                self.builder.instr().cmp(Condition::GreaterEqual, Bit1, lhs, rhs)
              }

              _ => unreachable!(),
            };

            RValue::bool(res)
          }
        };

        res
      }

      /*
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

        let first_ptr = self.builder.instr().load(Bit64, MemFlags::new(), array_ptr, 0);

        let slot_size = ret_dvt.len(self.ctx);
        let slot_size = self.builder.instr().iconst(Bit64, slot_size as i64 * 8);

        let index = rhs.unwrap_single(self);

        let offset = self.builder.instr().imul(index, slot_size);
        let element_ptr = self.builder.instr().iadd(first_ptr, offset);

        match ret_dvt {
          DynamicValueType::Const(vt) => RValue::TypedPtr(vt, element_ptr),
          DynamicValueType::Union(len) => RValue::UntypedPtr(len, element_ptr),
        }
      }
      */
      mir::Expr::If { cond, then, els: None, ty: _ } => {
        let (cond, a, b) = self.compile_conditional(cond);

        self.builder.current_block().id();
        let merge_block = self.builder.new_block().id();

        self.builder.instr().branch(cond.invert(), merge_block, Bit64, a, b);
        self.compile_expr(then);
        self.builder.current_block().terminate(TerminatorInstruction::Jump(merge_block));

        self.builder.switch_to(merge_block);

        RValue::nil()
      }

      mir::Expr::If { cond, then, els: Some(els), ref ty } => {
        let vt = ValueType::for_type(self.mir(), ty);

        let (cond, a, b) = self.compile_conditional(cond);

        let then_block = self.builder.current_block().id();
        let else_block = self.builder.new_block().id();
        let merge_block = self.builder.new_block().id();

        self.builder.instr().branch(cond.invert(), else_block, Bit64, a, b);
        let then_res = self.compile_expr(then);
        self.builder.current_block().terminate(TerminatorInstruction::Jump(merge_block));

        self.builder.switch_to(else_block);
        let else_res = self.compile_expr(els);
        self.builder.current_block().terminate(TerminatorInstruction::Jump(merge_block));

        self.builder.switch_to(merge_block);

        if vt == ValueType::Nil {
          RValue::nil()
        } else {
          let then_res = then_res.to_ir(self);
          let else_res = else_res.to_ir(self);

          assert_eq!(then_res.len(), else_res.len(), "mismatched branches in if expression");

          let mut res = vec![];
          for (t, e) in then_res.into_iter().zip(else_res.into_iter()) {
            res.push(
              self
                .builder
                .current_block()
                .phi([(then_block, Some(t)), (else_block, Some(e))].into_iter().collect()),
            );
          }

          RValue::new(vt, res)
        }

        /*
        } else if dvt.len(self.ctx) == 1 {
          // Special case: if `dvt.len() == 1`, we can avoid creating a stack slot, and
          // just use a block parameter.
          self.builder.append_block_param(merge_block, cranelift::codegen::Bit64);

          // Test the if condition and conditionally branch.
          self.builder.instr().brif(cond, then_block, &[], else_block, &[]);

          self.builder.switch_to_block(then_block);
          self.builder.seal_block(then_block);
          let then_return = self.compile_expr(then).to_ir(param_kind, self);

          self.builder.instr().jump(
            merge_block,
            &[match then_return {
              Slot::Single(v) => v,
              _ => unreachable!("cannot produce multiple values for a block with only 1 argument"),
            }],
          );

          self.builder.switch_to_block(else_block);
          self.builder.seal_block(else_block);
          let else_return = self.compile_expr(els).to_ir(param_kind, self);

          self.builder.instr().jump(
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
          let addr = self.builder.instr().stack_addr(Bit64, slot.clone(), 0);

          // Test the if condition and conditionally branch.
          self.builder.instr().brif(cond, then_block, &[], else_block, &[]);

          self.builder.switch_to_block(then_block);
          self.builder.seal_block(then_block);
          let then_return = self.compile_expr(then).to_ir(param_kind, self);
          then_return.copy_to(self, addr);

          self.builder.instr().jump(merge_block, &[]);

          self.builder.switch_to_block(else_block);
          self.builder.seal_block(else_block);
          let else_return = self.compile_expr(els).to_ir(param_kind, self);
          else_return.copy_to(self, addr);

          self.builder.instr().jump(merge_block, &[]);

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
        */
      }

      /*
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

          let addr = self.builder.instr().stack_addr(Bit64, slot.clone(), offset as i32 * 8);
          ir.copy_to(self, addr);
        }

        RValue::TypedDyn(ValueType::Struct(id), Slot::Multiple(len as usize, slot))
      }
      */
      ref v => unimplemented!("expr: {v:?}"),
    }
  }

  fn compile_conditional(&mut self, expr: mir::ExprId) -> (Condition, Variable, Variable) {
    match self.mir.exprs[expr] {
      mir::Expr::Binary(
        lhs,
        ref op @ (mir::BinaryOp::Eq
        | mir::BinaryOp::Neq
        | mir::BinaryOp::Lt
        | mir::BinaryOp::Lte
        | mir::BinaryOp::Gt
        | mir::BinaryOp::Gte),
        rhs,
        _,
      ) => {
        let lhs = self.compile_expr(lhs);
        let rhs = self.compile_expr(rhs);

        match op {
          mir::BinaryOp::Eq | mir::BinaryOp::Neq => match (lhs.const_ty(), rhs.const_ty()) {
            (Some(ValueType::Int), Some(ValueType::Int)) => {
              let l = lhs.unwrap_single(self);
              let r = rhs.unwrap_single(self);

              match op {
                mir::BinaryOp::Eq => (Condition::Equal, l, r),
                mir::BinaryOp::Neq => (Condition::NotEqual, l, r),
                _ => unreachable!(),
              }
            }

            (_, _) => todo!("equality for {lhs:?} and {rhs:?}"),
          },

          _ => {
            let lhs = lhs.unwrap_single(self);
            let rhs = rhs.unwrap_single(self);

            match op {
              mir::BinaryOp::Lt => (Condition::Less, lhs, rhs),
              mir::BinaryOp::Lte => (Condition::LessEqual, lhs, rhs),
              mir::BinaryOp::Gt => (Condition::Greater, lhs, rhs),
              mir::BinaryOp::Gte => (Condition::GreaterEqual, lhs, rhs),

              _ => unreachable!(),
            }
          }
        }
      }

      _ => {
        let cond = self.compile_expr(expr);

        (Condition::NotEqual, cond.unwrap_single(self), self.builder.instr().mov(Bit64, 0))
      }
    }
  }

  /*
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
      let addr = self.builder.instr().stack_addr(Bit64, arg_slot, slot_index as i32 * 8);
      ir.copy_to(self, addr);
      slot_index += ir.len();
    }

    let _arg_ptr = self.builder.instr().stack_addr(Bit64, arg_slot, 0);
    let _ret_ptr = self.builder.instr().stack_addr(Bit64, ret_slot, 0);

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
  */
}
