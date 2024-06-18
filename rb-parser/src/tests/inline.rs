//! This module greps parser's code for specially formatted comments and turns
//! them into tests.

use crate::{tests::format_events, Event};

use super::lex_events;
use std::{
  fs,
  path::{Path, PathBuf},
};

pub fn project_root() -> PathBuf {
  let dir = env!("CARGO_MANIFEST_DIR");
  let res = PathBuf::from(dir).parent().unwrap().to_owned();
  assert!(res.join("rustfmt.toml").exists());
  res
}

#[test]
fn grammar_inline_tests() {
  let grammar_dir = project_root().join(Path::new("rb-parser/src/grammar"));
  let tests = tests_from_dir(&grammar_dir);

  for test in tests {
    let mut found_error = None;
    let events = lex_events(crate::EntryPoint::SourceFile, &format!("{}\n", test.src));
    for event in &events {
      match event {
        Event::Error { msg } => found_error = Some(msg),
        _ => {}
      }
    }
    match (found_error, test.ok) {
      (Some(err), true) => {
        panic!(
          "test failed to parse: {} {err}\n{}",
          test.location,
          format_events(&events, &test.src)
        );
      }
      (None, false) => {
        panic!("test parsed ok but was expected to fail: {}", test.location);
      }
      _ => {}
    }
  }
}

#[derive(Debug)]
struct Test {
  location: String,
  src:      String,
  ok:       bool,
}

fn collect_tests(s: &str, location: &Path) -> Vec<Test> {
  let mut tests = vec![];
  let mut in_test = None;
  let mut test_lines = vec![];
  for (i, line) in s.lines().enumerate() {
    let line = line.trim();

    if let Some((line_num, ok)) = in_test {
      if let Some(l) = line.strip_prefix("// ") {
        test_lines.push(l);
      } else {
        tests.push(Test {
          location: format!("{}:{}", location.display(), line_num),
          src: test_lines.join("\n"),
          ok,
        });
        in_test = None;
        test_lines.clear();
      }
      continue;
    }

    if !line.starts_with("// test") {
      continue;
    }

    let ok = match line.split(' ').nth(2).unwrap_or("") {
      "ok" => true,
      "err" => false,
      other => {
        panic!(
          "invalid test annotation: {} at {}",
          other,
          format!("{}:{}", location.display(), i + 1)
        )
      }
    };

    in_test = Some((i + 1, ok));
  }

  tests
}

fn tests_from_dir(dir: &Path) -> Vec<Test> {
  let mut tests = vec![];
  for entry in dir.read_dir().unwrap() {
    let entry = entry.unwrap();
    let path = entry.path();
    if path.extension().unwrap_or_default() != "rs" {
      continue;
    }

    process_file(&mut tests, &path);
  }

  fn process_file(tests: &mut Vec<Test>, path: &Path) {
    let text = fs::read_to_string(path).unwrap();

    for test in collect_tests(&text, path) {
      tests.push(test);
    }
  }

  tests
}
