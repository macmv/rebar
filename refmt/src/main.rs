use rb_diagnostic::{emit, Source, Sources, Span};
use rb_syntax::cst;
use std::{
  io::Read,
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

  let source = if args.input == Path::new("-") {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    s
  } else {
    match std::fs::read_to_string(&args.input) {
      Ok(s) => s,
      Err(e) => {
        eprintln!("Failed to read file {}: {}", args.input.display(), e);
        std::process::exit(1);
      }
    }
  };

  let name = "input.rbr";
  let cst = cst::SourceFile::parse(&source);

  let mut sources = Sources::new();
  let file = sources.add(Source::new(name.into(), source));

  rb_diagnostic::run_or_exit(Arc::new(sources), || {
    for error in cst.errors() {
      emit!(error.message(), Span { file, range: error.span() });
    }
  });

  let out = fmt::format(&cst.tree());
  print!("{out}");
}
