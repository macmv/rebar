pub mod format;

mod grammar;
mod syntax_kind;
#[cfg(test)]
mod tests;
mod token;

use std::{mem, ops::Range};

use drop_bomb::DropBomb;
pub use syntax_kind::SyntaxKind;
use token::LexError;
pub use token::Lexer;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

#[cfg(test)]
#[macro_use]
extern crate rb_test;

pub enum EntryPoint {
  SourceFile,
  Expr,
}

struct Parser<'a> {
  lexer: &'a mut Lexer<'a>,

  current:            SyntaxKind,
  current_range:      Range<usize>,
  pending_whitespace: usize,

  events: Vec<Event>,

  peeked: Option<(SyntaxKind, Range<usize>)>,
}

/// `Parser` produces a flat list of `Event`s.
/// They are converted to a tree-structure in
/// a separate pass, via `TreeBuilder`.
#[derive(Debug)]
pub enum Event {
  /// This event signifies the start of the node.
  /// It should be either abandoned (in which case the
  /// `kind` is `TOMBSTONE`, and the event is ignored),
  /// or completed via a `Finish` event.
  ///
  /// All tokens between a `Start` and a `Finish` would
  /// become the children of the respective node.
  ///
  /// For left-recursive syntactic constructs, the parser produces
  /// a child node before it sees a parent. `forward_parent`
  /// saves the position of current event's parent.
  ///
  /// Consider this path
  ///
  /// foo::bar
  ///
  /// The events for it would look like this:
  ///
  /// ```text
  /// START(PATH) IDENT('foo') FINISH START(PATH) T![::] IDENT('bar') FINISH
  ///       |                          /\
  ///       |                          |
  ///       +------forward-parent------+
  /// ```
  ///
  /// And the tree would look like this
  ///
  /// ```text
  ///    +--PATH---------+
  ///    |   |           |
  ///    |   |           |
  ///    |  '::'       'bar'
  ///    |
  ///   PATH
  ///    |
  ///   'foo'
  /// ```
  ///
  /// See also `CompletedMarker::precede`.
  Start {
    kind:           SyntaxKind,
    forward_parent: Option<u32>,
  },

  /// Complete the previous `Start` event
  Finish,

  /// Produce a single leaf-element.
  Token {
    kind: SyntaxKind,
    len:  usize,
  },

  Error {
    msg: String,
  },
}
impl Event {
  pub fn tombstone() -> Self { Event::Token { kind: SyntaxKind::TOMBSTONE, len: 0 } }
}

impl EntryPoint {
  pub fn parse<'a>(&'a self, lexer: &'a mut Lexer<'a>) -> Vec<Event> {
    let mut parser = Parser::new(lexer);
    match self {
      EntryPoint::SourceFile => grammar::entry_point::source_file(&mut parser),
      EntryPoint::Expr => grammar::entry_point::expr(&mut parser),
    }
    parser.finish()
  }
}

impl<'a> Parser<'a> {
  pub fn new(lexer: &'a mut Lexer<'a>) -> Self {
    let first = match lexer.next() {
      Ok(t) => t,
      Err(_) => todo!(),
    };

    Parser {
      current_range: lexer.range(),
      lexer,
      current: first,
      events: Vec::new(),
      pending_whitespace: 0,
      peeked: None,
    }
  }
}

struct Marker {
  pos:  u32,
  bomb: DropBomb,
}

struct CompletedMarker {
  pos: u32,
}

impl Parser<'_> {
  pub fn finish(self) -> Vec<Event> { self.events }

  fn eat_trivia(&mut self) {
    if self.pending_whitespace > 0 {
      self
        .events
        .push(Event::Token { kind: SyntaxKind::WHITESPACE, len: self.pending_whitespace });
      self.pending_whitespace = 0;
    }
  }

  #[allow(dead_code)]
  pub fn peek(&mut self) -> SyntaxKind {
    if let Some((p, _)) = self.peeked {
      p
    } else {
      // Don't push an even here. Instead, we'll push `current` when we consume the
      // peeked token in `bump`.
      let t = self.bump_inner(false);
      self.peeked = Some((t, self.lexer.range()));
      t
    }
  }

  pub fn start(&mut self) -> Marker {
    self.eat_trivia();

    let i = self.events.len() as u32;
    self.events.push(Event::Start { kind: SyntaxKind::TOMBSTONE, forward_parent: None });
    Marker { pos: i, bomb: DropBomb::new("Marker must be either completed or abandoned") }
  }
  pub fn at(&mut self, t: SyntaxKind) -> bool { self.current() == t }
  pub fn current(&self) -> SyntaxKind { self.current }
  #[track_caller]
  pub fn eat(&mut self, t: SyntaxKind) {
    assert_eq!(self.current(), t, "eat got unexpected result");
    self.bump();
  }
  pub fn bump(&mut self) -> SyntaxKind {
    if let Some((t, r)) = self.peeked.take() {
      // Push `current`, now that we're pulling an event from `peeked`.
      self.events.push(Event::Token { kind: self.current, len: self.current_range.len() });
      self.current = t;
      self.current_range = r;
      t
    } else {
      let kind = self.bump_inner(true);
      self.current = kind;
      self.current_range = self.lexer.range();
      kind
    }
  }

  fn bump_inner(&mut self, push: bool) -> SyntaxKind {
    self.eat_trivia();
    if push {
      self.events.push(Event::Token { kind: self.current, len: self.lexer.slice().len() });
    }

    loop {
      match self.lexer.next() {
        // Ignore whitespace tokens here, because we usually don't care about them when parsing. We
        // record that they got skipped, so that we can recover them later if we need a concrete
        // tree.
        Ok(T![ws]) => {
          self.pending_whitespace += self.lexer.slice().len();
        }
        Ok(t) => break t,
        Err(LexError::Eof) => {
          self.eat_trivia();
          break SyntaxKind::EOF;
        }
        Err(e) => {
          self.error(e.to_string());
          break self.current;
        }
      }
    }
  }

  pub fn expect(&mut self, t: SyntaxKind) {
    if self.current() != t {
      self.error(format!("expected {t}"));
    } else {
      self.bump();
    }
  }

  pub fn error(&mut self, msg: impl Into<String>) {
    self.events.push(Event::Error { msg: msg.into() })
  }
}

impl Marker {
  pub fn complete(mut self, parser: &mut Parser, kind: SyntaxKind) -> CompletedMarker {
    self.bomb.defuse();
    match &mut parser.events[self.pos as usize] {
      Event::Start { kind: k, .. } => *k = kind,
      _ => unreachable!(),
    }
    parser.events.push(Event::Finish);
    CompletedMarker { pos: self.pos }
  }

  pub fn abandon(mut self, parser: &mut Parser) {
    self.bomb.defuse();

    #[cfg(debug_assertions)]
    match parser.events[self.pos as usize] {
      Event::Start { kind: SyntaxKind::TOMBSTONE, forward_parent: None } => (),
      _ => unreachable!(),
    }

    if self.pos as usize == parser.events.len() - 1 {
      match parser.events.pop() {
        // Sanity check
        Some(Event::Start { kind: SyntaxKind::TOMBSTONE, forward_parent: None }) => (),
        _ => unreachable!(),
      }
    }
  }
}

impl CompletedMarker {
  fn precede(self, p: &mut Parser) -> Marker {
    let new_pos = p.start();
    let idx = self.pos as usize;
    match &mut p.events[idx] {
      Event::Start { forward_parent, .. } => {
        *forward_parent = Some(new_pos.pos - self.pos);
      }
      _ => unreachable!(),
    }
    new_pos
  }
}

// Removes all the forward_parents. TODO: Produce a new Output type or something
// to avoid exposing Event.
pub fn process_events(events: &mut [Event]) -> Vec<Event> {
  let mut out = vec![];
  let mut forward_parents = Vec::new();

  for i in 0..events.len() {
    match mem::replace(&mut events[i], Event::tombstone()) {
      Event::Start { kind, forward_parent } => {
        // For events[A, B, C], B is A's forward_parent, C is B's forward_parent,
        // in the normal control flow, the parent-child relation: `A -> B -> C`,
        // while with the magic forward_parent, it writes: `C <- B <- A`.

        // append `A` into parents.
        forward_parents.push(kind);
        let mut idx = i;
        let mut fp = forward_parent;
        while let Some(fwd) = fp {
          idx += fwd as usize;
          // append `A`'s forward_parent `B`
          fp = match mem::replace(&mut events[idx], Event::tombstone()) {
            Event::Start { kind, forward_parent } => {
              forward_parents.push(kind);
              forward_parent
            }
            _ => unreachable!(),
          };
          // append `B`'s forward_parent `C` in the next stage.
        }

        for kind in forward_parents.drain(..).rev() {
          if kind != SyntaxKind::TOMBSTONE {
            out.push(Event::Start { kind, forward_parent: None });
          }
        }
      }
      Event::Finish => {
        out.push(Event::Finish);
      }
      Event::Token { kind, len } => {
        if kind != SyntaxKind::TOMBSTONE {
          out.push(Event::Token { kind, len });
        }
      }
      Event::Error { msg } => out.push(Event::Error { msg }),
    }
  }

  out
}
