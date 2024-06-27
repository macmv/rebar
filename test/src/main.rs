use std::path::{Path, PathBuf};

fn main() {
  let files = gather_files(Path::new("test/integration"));

  println!("running tests...");

  for path in files {
    if path.extension().unwrap() == "rbr" {
      print!("{}...", path.display());

      let source = std::fs::read_to_string(&path).unwrap();
      rb_runtime::eval(&source);

      println!(" \x1b[32mok\x1b[0m");
    }
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
