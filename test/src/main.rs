use std::{
  panic::catch_unwind,
  path::{Path, PathBuf},
  process::ExitCode,
  sync::atomic::Ordering,
};

fn main() -> ExitCode {
  let filter = std::env::args().nth(1).unwrap_or_default();

  let mut files = gather_files(Path::new("test/integration"));
  files.retain(|path| path.display().to_string().contains(&filter));

  println!("running tests...");

  const NUM_CPUS: usize = 32;
  let chunk_size = (files.len() / NUM_CPUS).max(1);

  let failed = std::sync::atomic::AtomicBool::new(false);
  let std = Path::new("lib/std/lib.rbr");

  let out_dir = Path::new("out");
  std::fs::remove_dir_all(&out_dir).unwrap();
  std::fs::create_dir_all(&out_dir).unwrap();

  std::thread::scope(|scope| {
    for chunk in files.chunks(chunk_size) {
      let failed = &failed;
      scope.spawn(move || {
        for path in chunk {
          let name = path.file_stem().unwrap().to_string_lossy();
          let stringified = path.display().to_string();
          let object = out_dir.join(format!("{name}.o"));
          let _binary = out_dir.join(&*name);

          let res = catch_unwind(|| match rb_runtime::compile_test(path, std, &object) {
            (_, Ok(_)) => println!("{}... \x1b[32mok\x1b[0m", stringified),
            (sources, Err(diagnostics)) => {
              failed.fetch_or(true, Ordering::AcqRel);
              println!("{}... \x1b[31mfail\x1b[0m", stringified);
              for d in diagnostics {
                println!("{}", d.render_with_color(&sources));
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
      });
    }
  });

  if failed.into_inner() { ExitCode::FAILURE } else { ExitCode::SUCCESS }
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
    } else if path.extension().is_some_and(|e| e == "rbr") {
      files.push(path);
    }
  }
}
