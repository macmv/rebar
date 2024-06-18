use crate::{format::format_events, EntryPoint, Event, Lexer};

mod inline;

pub fn lex_events(entry_point: EntryPoint, text: &str) -> Vec<Event> {
  let mut events = entry_point.parse(&mut Lexer::new(text));

  crate::process_events(&mut events)
}
