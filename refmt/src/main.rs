use rb_diagnostic::{emit, Source, Sources, Span};
use rb_syntax::cst;
use std::{path::PathBuf, sync::Arc};

use clap::Parser;

#[derive(Parser)]
struct Args {
  input: PathBuf,
}

fn main() {
  let args = Args::parse();

  let source = match std::fs::read_to_string(&args.input) {
    Ok(s) => s,
    Err(e) => {
      eprintln!("Failed to read file {}: {}", args.input.display(), e);
      std::process::exit(1);
    }
  };

  let name = args.input.to_string_lossy().into_owned();
  let cst = cst::SourceFile::parse(&source);

  let mut sources = Sources::new();
  let file = sources.add(Source::new(name, source));

  rb_diagnostic::run_or_exit(Arc::new(sources), || {
    for error in cst.errors() {
      emit!(error.message(), Span { file, range: error.span() });
    }
  });

  println!("Hello, world!");
}
