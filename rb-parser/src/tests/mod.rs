use crate::{format::format_events, EntryPoint, Event, Lexer};
use rb_test::Expect;

mod inline;

pub fn check_expr(input: &str, expected_tree: Expect) {
  check_inner(EntryPoint::Expr, input, expected_tree);
}
pub fn check(input: &str, expected_tree: Expect) {
  check_inner(EntryPoint::SourceFile, input, expected_tree);
}

fn check_inner(entry_point: EntryPoint, text: &str, expected_tree: Expect) {
  let actual_tree = lex(entry_point, text);

  expected_tree.assert_eq(&actual_tree);
}

pub fn lex(entry_point: EntryPoint, text: &str) -> String {
  crate::format::format_events(&lex_events(entry_point, text), text)
}

pub fn lex_events(entry_point: EntryPoint, text: &str) -> Vec<Event> {
  let mut events = entry_point.parse(&mut Lexer::new(text));

  crate::process_events(&mut events)
}
