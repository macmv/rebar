use std::{collections::HashMap, sync::Arc};

use rb_diagnostic::{Diagnostic, Sources};
use rb_hir::ast::{Path, Type};
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
  let (mir_ctx, function_map, functions) = build_environment(&mut env, &module, &span_map);

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
        if let Some(mut func) = rb_mir_lower::lower_function(&mir_ctx, &typer, function) {
          func.id = *id;

          return Some(func);
        }
      }

      None
    },
  );

  rb_diagnostic::check()?;

  let mut functions = functions.into_iter().flatten().collect::<Vec<_>>();

  let start_id = rb_mir::ast::UserFunctionId(functions.len() as u64);
  functions.push(generate_start_func(main_func, start_id));

  // If we get to this point, all checks have passed, and we can compile to
  // cranelift IR. Collect all the functions, split them into chunks, and compile
  // them on a thread pool.

  compile_mir(mir_ctx, functions, start_id, out);

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
  mir_ctx: MirContext,
  functions: Vec<rb_mir::ast::Function>,
  main_func: rb_mir::ast::UserFunctionId,
  out: &std::path::Path,
) {
  let mut compiler = rb_backend::Compiler::new(mir_ctx);

  for func in &functions {
    compiler.declare_function(func);
  }

  let compiled =
    run_parallel(&functions, || compiler.new_thread(), |ctx, f| ctx.compile_function(f));

  for func in compiled.into_iter() {
    compiler.finish_function(func);
  }

  compiler.finish(main_func, out);

  let name = out.file_stem().unwrap().to_string_lossy();

  let status = std::process::Command::new("wild")
    .arg(out)
    .arg("-o")
    .arg(out.parent().unwrap().join(&*name))
    .status()
    .unwrap();
  if !status.success() {
    panic!("linker failed");
  }
}

fn build_environment<'a>(
  env: &mut rb_hir::Environment,
  module: &'a rb_hir::ast::Module,
  span_map: &'a rb_hir::SpanMap,
) -> (
  rb_mir::MirContext,
  HashMap<Path, rb_mir::ast::UserFunctionId>,
  Vec<(rb_mir::ast::UserFunctionId, &'a rb_hir::ast::Function, &'a rb_hir::FunctionSpanMap)>,
) {
  let mut mir_ctx = MirContext::default();
  let mut functions = vec![];
  let mut function_map = HashMap::new();
  let mut struct_id = rb_mir::ast::StructId(0);

  for (path, module) in module.modules() {
    let span_map = &span_map.modules[&path];
    for s in module.structs.values() {
      let struct_path = path.join(s.name.clone());

      env.structs.insert(
        struct_path.clone(),
        s.fields.iter().map(|(name, te)| (name.clone(), rb_typer::type_of_type_expr(te))).collect(),
      );
      mir_ctx.struct_paths.insert(struct_path, struct_id);
      mir_ctx.structs.insert(
        struct_id,
        rb_mir::Struct {
          fields: s
            .fields
            .iter()
            .map(|(name, te)| (name.clone(), rb_typer::type_of_type_expr(te)))
            .collect(),
        },
      );
      struct_id.0 += 1;
    }

    for (hir_id, f) in module.functions.iter() {
      let path = path.join(f.name.clone());
      let span_map = &span_map.functions[&hir_id];

      let mir_id = rb_mir::ast::UserFunctionId(functions.len() as u64);
      functions.push((mir_id, f, span_map));
      function_map.insert(path.clone(), mir_id);
      rb_mir_lower::declare_user_function(&mut mir_ctx, mir_id, path.clone(), f, span_map);
      env.names.insert(
        rb_hir::ast::FullyQualifiedName::new_bare(path).unwrap(),
        rb_typer::type_of_function(f),
      );
    }
  }

  (mir_ctx, function_map, functions)
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
