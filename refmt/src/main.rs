use rb_diagnostic::{emit, Source, Sources, Span};
use rb_syntax::cst;
use std::{io::Read, path::PathBuf, sync::Arc};

use clap::Parser;

mod fmt;

#[derive(Parser)]
struct Args {
  #[clap(short, long)]
  input: Option<PathBuf>,

  #[clap(long)]
  stdin: bool,
}

fn main() {
  let args = Args::parse();

  let source = if let Some(ref input) = args.input {
    if args.stdin {
      eprintln!("Cannot specify both --input and --stdin");
      std::process::exit(1);
    }

    match std::fs::read_to_string(input) {
      Ok(s) => s,
      Err(e) => {
        eprintln!("Failed to read file {}: {}", input.display(), e);
        std::process::exit(1);
      }
    }
  } else if args.stdin {
    if args.input.is_some() {
      eprintln!("Cannot specify both --input and --stdin");
      std::process::exit(1);
    }

    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    s
  } else {
    eprintln!("Must specify either --input or --stdin");
    std::process::exit(1);
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
