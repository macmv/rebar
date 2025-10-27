use rb_diagnostic::{Source, Sources, Span, emit};
use rb_syntax::cst;
use std::{
  io::{self, Read},
  path::{Path, PathBuf},
  sync::Arc,
};

use clap::Parser;

mod fmt;

#[cfg(test)]
mod tests;

#[derive(Parser)]
struct Args {
  #[arg()]
  input: PathBuf,
}

fn main() {
  let args = Args::parse();

  let res = if args.input == Path::new("-") {
    format_stdin()
  } else if args.input.is_dir() {
    format_dir(&args.input)
  } else {
    format_file(&args.input)
  };

  match res {
    Ok(_) => {}
    Err(err) => {
      eprintln!("{}", err);
      std::process::exit(1);
    }
  }
}

fn format_stdin() -> Result<(), io::Error> {
  let mut source = String::new();
  io::stdin().read_to_string(&mut source)?;

  let formatted = format_str(source)?;

  print!("{}", formatted);

  Ok(())
}

fn format_dir(dir: &Path) -> Result<(), io::Error> {
  for entry in std::fs::read_dir(dir)? {
    let entry = entry?;
    let path = entry.path();

    if path.is_dir() {
      format_dir(&path)?;
    } else if path.extension().is_some_and(|ext| ext == "rbr") {
      format_file(&path)?;
    }
  }

  Ok(())
}

fn format_file(path: &Path) -> Result<(), io::Error> {
  let source = std::fs::read_to_string(path)?;

  let formatted = format_str(source)?;

  std::fs::write(path, formatted)
}

fn format_str(source: String) -> Result<String, io::Error> {
  let name = "input.rbr";
  let cst = cst::SourceFile::parse(&source);

  let mut sources = Sources::new();
  let file = sources.add(Source::new(name.into(), source));

  rb_diagnostic::run_or_exit(Arc::new(sources), || {
    for error in cst.errors() {
      emit!(Span { file, range: error.span() } => error.message());
    }
  });

  Ok(fmt::format(&cst.tree()))
}
