use std::sync::Arc;

use rb_diagnostic::{Diagnostic, Sources};
use rb_hir::ast::Type;
use rb_mir::{MirContext, ast as mir};

const NUM_CPUS: usize = 32;

pub fn compile(path: &std::path::Path) -> (Sources, Result<(), Vec<Diagnostic>>) {
  let (sources, res) = rb_hir_lower::parse_hir(&rb_hir_lower::fs::Native, path);
  let (mut hir, span_map) = match res {
    Ok(v) => v,
    Err(diagnostics) => return (sources, Err(diagnostics)),
  };

  let sources = Arc::new(sources);

  let env = rb_hir::Environment::empty();

  let res = rb_diagnostic::run(sources.clone(), || {
    rb_hir_lower::resolve_hir(&env, &mut hir, &span_map);
    compile_diagnostics(env, hir, span_map, std::path::Path::new("out.o"))
  })
  .map(|_| ());
  (Arc::try_unwrap(sources).unwrap_or_else(|_| panic!()), res)
}

pub fn compile_test(
  test_path: &std::path::Path,
  std: &std::path::Path,
  out: &std::path::Path,
) -> (Sources, Result<(), Vec<Diagnostic>>) {
  let (mut sources, res) = rb_hir_lower::parse_hir(&rb_hir_lower::fs::Native, std);
  let (mut hir, mut span_map) = match res {
    Ok(v) => v,
    Err(diagnostics) => return (sources, Err(diagnostics)),
  };

  let (new_sources, res) =
    rb_hir_lower::parse_source(&rb_hir_lower::fs::Native, test_path, sources);
  sources = new_sources;
  let (test_module, test_span_map) = match res {
    Ok((hir, span_map, _)) => (hir, span_map),
    Err(diagnostics) => return (sources, Err(diagnostics)),
  };

  hir.modules.insert("test".into(), rb_hir::ast::PartialModule::Inline(test_module));
  span_map.modules.insert(rb_hir::ast::Path { segments: vec!["test".into()] }, test_span_map);

  let sources = Arc::new(sources);
  let env = rb_hir::Environment::empty();

  let res = rb_diagnostic::run(sources.clone(), || {
    rb_hir_lower::resolve_hir(&env, &mut hir, &span_map);
    compile_diagnostics(env, hir, span_map, out)
  })
  .map(|_| ());
  (Arc::try_unwrap(sources).unwrap_or_else(|_| panic!()), res)
}

fn compile_diagnostics(
  mut env: rb_hir::Environment,
  module: rb_hir::ast::Module,
  span_map: rb_hir::SpanMap,
  out: &std::path::Path,
) -> Result<(), ()> {
  rb_typer::scan_module(&module, &mut env);
  let (mir_ctx, function_map, functions) = rb_mir_lower::scan_module(&module, &span_map);

  let main_func = function_map
    .get(&rb_hir::ast::Path { segments: vec!["test".into(), "".into()] })
    .cloned()
    .ok_or_else(|| {
      panic!("no main function found");
    })?;

  rb_diagnostic::check()?;

  let functions = run_parallel(
    &functions,
    || (),
    |_, (id, function, span_map)| {
      let typer = rb_typer::Typer::check(&env, function, span_map);

      if rb_diagnostic::is_ok() {
        Some(if function.ext.is_some() {
          Func::Extern(*id, function.name.clone())
        } else {
          let mut func = rb_mir_lower::lower_function(&mir_ctx, &typer, function);
          func.id = *id;
          if !function.name.is_empty() {
            func.debug_name = Some(function.name.clone());
          }
          Func::UserDefined(func)
        })
      } else {
        None
      }
    },
  );

  rb_diagnostic::check()?;

  let mut functions = functions.into_iter().flatten().collect::<Vec<_>>();

  let entry_id = rb_mir::ast::FunctionId(functions.len() as u64);
  functions.push(Func::UserDefined(generate_entry_func(main_func, entry_id)));

  // If we get to this point, all checks have passed, and we can compile to
  // cranelift IR. Collect all the functions, split them into chunks, and compile
  // them on a thread pool.

  compile_mir(mir_ctx, functions, entry_id, out);

  Ok(())
}

fn generate_entry_func(main_func: mir::FunctionId, entry_id: mir::FunctionId) -> mir::Function {
  let mut entry_func = mir::Function::default();
  entry_func.id = entry_id;

  let call = entry_func.exprs.alloc(mir::Expr::Call(
    main_func,
    Type::Function(vec![], Box::new(Type::unit())),
    vec![],
  ));
  entry_func.items.push(entry_func.stmts.alloc(mir::Stmt::Expr(call)));

  let exit_syscall = entry_func.exprs.alloc(mir::Expr::Literal(mir::Literal::Int(60)));
  let exit_code = entry_func.exprs.alloc(mir::Expr::Literal(mir::Literal::Int(0)));
  let exit = entry_func
    .exprs
    .alloc(mir::Expr::CallIntrinsic(mir::Intrinsic::Syscall, vec![exit_syscall, exit_code]));
  entry_func.items.push(entry_func.stmts.alloc(mir::Stmt::Expr(exit)));

  let trap = entry_func.exprs.alloc(mir::Expr::CallIntrinsic(mir::Intrinsic::Trap, vec![]));
  entry_func.items.push(entry_func.stmts.alloc(mir::Stmt::Expr(trap)));

  entry_func
}

enum Func {
  UserDefined(mir::Function),
  Extern(mir::FunctionId, String),
}

fn compile_mir(
  mir_ctx: MirContext,
  functions: Vec<Func>,
  entry_func: rb_mir::ast::FunctionId,
  out: &std::path::Path,
) {
  let mut compiler = rb_backend::Compiler::new(mir_ctx);

  for func in &functions {
    match func {
      Func::UserDefined(f) => compiler.declare_function(f),
      Func::Extern(f, name) => compiler.declare_extern_function(f, name),
    }
  }

  let compiled = run_parallel(
    &functions,
    || compiler.new_thread(),
    |ctx, f| match f {
      Func::UserDefined(f) => Some(ctx.compile_function(f)),
      Func::Extern(_, _) => None,
    },
  );

  for func in compiled.into_iter().flatten() {
    compiler.finish_function(func);
  }

  compiler.finish(entry_func, out);

  let name = out.file_stem().unwrap().to_string_lossy();

  let status = std::process::Command::new("clang")
    .arg("-fuse-ld=/usr/bin/wild")
    .arg(out)
    .arg("-o")
    .arg(out.parent().unwrap().join(&*name))
    .status()
    .unwrap();
  if !status.success() {
    panic!("linker failed");
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

  rb_diagnostic::scope(|scope| {
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
