use std::{
  panic::catch_unwind,
  path::{Path, PathBuf},
  process::ExitCode,
  sync::{atomic::Ordering, Arc},
};

use rb_diagnostic::{Source, Sources};
use rb_runtime::RuntimeEnvironment;

fn main() -> ExitCode {
  let filter = std::env::args().nth(1).unwrap_or_default();

  let files = gather_files(Path::new("test/integration"));

  println!("running tests...");

  const NUM_CPUS: usize = 32;
  let chunk_size = (files.len() / NUM_CPUS).max(1);

  let failed = std::sync::atomic::AtomicBool::new(false);

  rb_runtime::parse_hir(Path::new("lib/std/lib.rbr")).unwrap_or_else(|_| panic!());

  let mut std = Sources::new();
  for src in std::fs::read_dir("lib/std").unwrap() {
    let src = src.unwrap();
    let path = src.path();
    if path.extension().is_some_and(|e| e == "rbr") {
      let content = std::fs::read_to_string(&path).unwrap();
      std.add(Source::new(path.display().to_string(), content));
    }
  }

  std::thread::scope(|scope| {
    for chunk in files.chunks(chunk_size) {
      let f = &filter;
      let failed = &failed;
      let std = &std;
      scope.spawn(move || {
        for path in chunk {
          if path.extension().unwrap() == "rbr" {
            let stringified = path.display().to_string();
            if stringified.contains(f) {
              let src = std::fs::read_to_string(path).unwrap();

              let mut sources = std.clone();
              let id = sources.add(Source::new(stringified.clone(), src.clone()));
              let sources = Arc::new(sources);

              let res = catch_unwind(|| {
                let env = RuntimeEnvironment::new();
                match rb_runtime::run(env, sources.clone(), id) {
                  Ok(_) => println!("{}... \x1b[32mok\x1b[0m", stringified),
                  Err(diagnostics) => {
                    failed.fetch_or(true, Ordering::AcqRel);
                    println!("{}... \x1b[31mfail\x1b[0m", stringified);
                    for d in diagnostics {
                      println!("{}", d.render(&sources));
                    }
                  }
                }
              });

              match res {
                Ok(_) => {}
                Err(e) => {
                  failed.fetch_or(true, Ordering::AcqRel);
                  println!("{}... \x1b[31mpanic\x1b[0m", stringified);

                  if let Some(s) = e.downcast_ref::<String>() {
                    println!("{}", s);
                  } else if let Some(s) = e.downcast_ref::<&str>() {
                    println!("{}", s);
                  } else {
                    println!("{:?}", e);
                  }
                }
              }
            }
          }
        }
      });
    }
  });

  if failed.into_inner() {
    ExitCode::FAILURE
  } else {
    ExitCode::SUCCESS
  }
}

fn gather_files(dir: &Path) -> Vec<PathBuf> {
  let mut files = Vec::new();

  gather_files_inner(dir, &mut files);

  files
}

fn gather_files_inner(dir: &Path, files: &mut Vec<PathBuf>) {
  for entry in std::fs::read_dir(dir).unwrap() {
    let entry = entry.unwrap();
    let path = entry.path();
    if path.is_dir() {
      files.extend(gather_files(&path));
    } else {
      files.push(path);
    }
  }
}
