use std::path::{Path, PathBuf};

fn main() {
  let filter = std::env::args().nth(1).unwrap_or_default();

  let files = gather_files(Path::new("test/integration"));

  println!("running tests...");

  const NUM_CPUS: usize = 32;
  let chunk_size = (files.len() / NUM_CPUS).max(1);

  std::thread::scope(|scope| {
    for chunk in files.chunks(chunk_size) {
      let f = &filter;
      scope.spawn(move || {
        for path in chunk {
          if path.extension().unwrap() == "rbr" {
            let stringified = path.display().to_string();
            if stringified.contains(f) {
              let source = std::fs::read_to_string(&path).unwrap();
              rb_runtime::eval(&source);

              println!("{}... \x1b[32mok\x1b[0m", stringified);
            }
          }
        }
      });
    }
  });
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
