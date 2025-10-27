use std::sync::Arc;

use rb_diagnostic::{emit, Diagnostic, Source, SourceId, Sources, Span};
use rb_mir::{ast as mir, MirContext};
use rb_syntax::cst;
use rb_typer::Type;

const NUM_CPUS: usize = 32;

#[derive(Default)]
pub struct RuntimeEnvironment {
  pub mir: MirContext,
}

pub fn eval(src: &str) {
  let env = RuntimeEnvironment::new();

  let mut sources = Sources::new();
  let id = sources.add(Source::new("inline.rbr".into(), src.into()));
  let sources = Arc::new(sources);

  rb_diagnostic::run_or_exit(sources.clone(), || compile_diagnostics(env, sources, id))
    .expect("error with no diagnostics emitted");
}

pub fn run(
  env: RuntimeEnvironment,
  sources: Arc<Sources>,
  id: SourceId,
) -> Result<(), Vec<Diagnostic>> {
  rb_diagnostic::run(sources.clone(), || compile_diagnostics(env, sources, id)).map(|_| ())
}

fn compile_diagnostics(
  mut env: RuntimeEnvironment,
  sources: Arc<Sources>,
  main: SourceId,
) -> Result<(), ()> {
  let results = run_parallel(
    &sources.all().collect::<Vec<_>>(),
    || (),
    |_, &id| {
      let src = sources.get(id);
      let res = cst::SourceFile::parse(&src.source);

      let (hir, span_maps, _) = if res.errors().is_empty() {
        rb_hir_lower::lower_source(res.tree(), id)
      } else {
        for error in res.errors() {
          emit!(Span { file: id, range: error.span() } => error.message());
        }

        return Err(());
      };

      Ok((hir, span_maps))
    },
  );

  rb_diagnostic::check()?;

  let files = results.into_iter().map(|r| r.unwrap()).collect::<Vec<_>>();

  let mut funcs = vec![];
  let mut main_func = rb_mir::ast::UserFunctionId(0);
  for (source_id, (hir, span_map)) in files.iter().enumerate() {
    for (id, function) in hir.functions.iter() {
      let span_map = &span_map.functions[&id];
      let mir_id = rb_mir::ast::UserFunctionId(funcs.len() as u64);
      funcs.push((mir_id, function, span_map));
    }
    if main.into_raw().into_u32() as usize == source_id {
      main_func = funcs.last().unwrap().0;
    }
  }

  let (typer_env, mir_env) = env.build(&files, &funcs);

  rb_diagnostic::check()?;

  let functions = run_parallel(
    &funcs,
    || (),
    |_, (id, function, span_map)| {
      let typer = rb_typer::Typer::check(&typer_env, function, span_map);

      if rb_diagnostic::is_ok() {
        if let Some(mut func) = rb_mir_lower::lower_function(&mir_env, &typer, function) {
          func.id = *id;

          return Some(func);
        }
      }

      None
    },
  );

  rb_diagnostic::check()?;

  let mut functions = functions.into_iter().flatten().collect::<Vec<_>>();

  let start_id = rb_mir::ast::UserFunctionId(funcs.len() as u64);
  functions.push(generate_start_func(main_func, start_id));

  // If we get to this point, all checks have passed, and we can compile to
  // cranelift IR. Collect all the functions, split them into chunks, and compile
  // them on a thread pool.

  compile_mir(env, functions, start_id);

  Ok(())
}

fn generate_start_func(
  main_func: mir::UserFunctionId,
  start_id: mir::UserFunctionId,
) -> mir::Function {
  let mut start_func = mir::Function::default();
  start_func.id = start_id;

  let call = start_func.exprs.alloc(mir::Expr::Call(
    main_func,
    Type::Function(vec![], Box::new(Type::unit())),
    vec![],
  ));
  start_func.items.push(start_func.stmts.alloc(mir::Stmt::Expr(call)));

  let exit_syscall = start_func.exprs.alloc(mir::Expr::Literal(mir::Literal::Int(60)));
  let exit_code = start_func.exprs.alloc(mir::Expr::Literal(mir::Literal::Int(0)));
  let exit = start_func
    .exprs
    .alloc(mir::Expr::CallIntrinsic(mir::Intrinsic::Syscall, vec![exit_syscall, exit_code]));
  start_func.items.push(start_func.stmts.alloc(mir::Stmt::Expr(exit)));

  let trap = start_func.exprs.alloc(mir::Expr::CallIntrinsic(mir::Intrinsic::Trap, vec![]));
  start_func.items.push(start_func.stmts.alloc(mir::Stmt::Expr(trap)));

  start_func
}

fn compile_mir(
  env: RuntimeEnvironment,
  functions: Vec<rb_mir::ast::Function>,
  main_func: rb_mir::ast::UserFunctionId,
) {
  let mut compiler = rb_backend::Compiler::new(env.mir.clone());

  for func in &functions {
    compiler.declare_function(func);
  }

  let compiled =
    run_parallel(&functions, || compiler.new_thread(), |ctx, f| ctx.compile_function(f));

  for func in compiled.into_iter() {
    compiler.finish_function(func);
  }

  compiler.finish(main_func);
}

impl RuntimeEnvironment {
  pub fn new() -> Self { RuntimeEnvironment::default() }

  fn build(
    &mut self,
    files: &[(rb_hir::ast::Module, rb_hir::SpanMap)],
    functions: &[(rb_mir::ast::UserFunctionId, &rb_hir::ast::Function, &rb_hir::FunctionSpanMap)],
  ) -> (rb_typer::Environment, rb_mir_lower::Env<'_>) {
    let mut typer_env = rb_typer::Environment::empty();

    for (hir, _) in files {
      for (id, s) in hir.structs.values().enumerate() {
        let id = rb_mir::ast::StructId(id as u64);

        typer_env.structs.insert(
          s.name.clone(),
          s.fields
            .iter()
            .map(|(name, te)| (name.clone(), rb_typer::type_of_type_expr(te)))
            .collect(),
        );
        self.mir.struct_paths.insert(s.name.clone(), id);
        self.mir.structs.insert(
          id,
          rb_mir::Struct {
            fields: s
              .fields
              .iter()
              .map(|(name, te)| (name.clone(), rb_typer::type_of_type_expr(te)))
              .collect(),
          },
        );
      }
    }

    let mut mir_env = self.mir_env();
    for (id, f, span_map) in functions {
      mir_env.declare_user_function(*id, f, span_map);
      typer_env.names.insert(f.name.clone(), rb_typer::type_of_function(f));
    }

    (typer_env, mir_env)
  }

  fn mir_env(&self) -> rb_mir_lower::Env<'_> {
    rb_mir_lower::Env { ctx: &self.mir, items: Default::default() }
  }
}

pub fn run_parallel<I: Send + Sync, C: Send, O: Send + Sync>(
  input: &[I],
  mut ctx: impl (FnMut() -> C) + Copy,
  mut f: impl (FnMut(&mut C, &I) -> O) + Copy + Send,
) -> Vec<O> {
  if input.len() < NUM_CPUS {
    let mut out = Vec::with_capacity(input.len());
    let mut ctx = ctx();

    for i in input {
      out.push(f(&mut ctx, i));
    }

    return out;
  };

  let chunk_size = (input.len() / NUM_CPUS).max(1);

  let mut results = vec![];
  for _ in 0..NUM_CPUS {
    results.push(Vec::with_capacity(chunk_size));
  }

  std::thread::scope(|scope| {
    for (chunk, out) in input.chunks(chunk_size).zip(results.iter_mut()) {
      let mut ctx = ctx();

      scope.spawn(move || {
        for i in chunk {
          out.push(f(&mut ctx, i));
        }
      });
    }
  });

  results.into_iter().flatten().collect()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  #[ignore] // TODO: Add `assert_eq`
  fn foo() {
    eval(
      r#"
        assert_eq(2 * 3 + 4 + 5, 15)
        4
      "#,
    );
  }
}
