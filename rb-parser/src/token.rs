use std::ops::Range;

use thiserror::Error;

use crate::{SyntaxKind, T};

pub type Result<T> = std::result::Result<T, LexError>;

#[derive(Debug, Error, PartialEq)]
pub enum LexError {
  #[error("invalid character")]
  InvalidChar,

  #[error("end of file reached")]
  Eof,
}

struct Tokenizer<'a> {
  source: &'a str,
  index:  usize,
}

impl<'a> Tokenizer<'a> {
  pub fn new(source: &'a str) -> Self { Tokenizer { source, index: 0 } }

  pub fn pos(&self) -> usize { self.index }

  pub fn peek(&mut self) -> Result<Option<SyntaxKind>> {
    if self.index >= self.source.len() {
      Ok(None)
    } else {
      let chars = self.source[self.index..].chars().take(1);
      let t1 = self.eat();
      for c in chars {
        self.index -= c.len_utf8();
      }
      Ok(Some(t1?))
    }
  }

  pub fn eat(&mut self) -> Result<SyntaxKind> {
    let Some(c) = self.source[self.index..].chars().next() else {
      return Err(LexError::Eof);
    };
    self.index += c.len_utf8();
    let t = match c {
      '\u{0020}' | '\u{0009}' | '\u{000d}' => T![ws],
      '\n' => T![nl],

      '(' => T!['('],
      ')' => T![')'],
      '[' => T!['['],
      ']' => T![']'],
      '{' => T!['{'],
      '}' => T!['}'],

      '+' => T![+],
      '-' => T![-],
      '=' => T![=],
      // '\'' => T!['\''],
      '"' => T!['"'],
      '.' => T![.],
      '!' => T![!],
      '&' => T![&],
      '|' => T![|],
      ',' => T![,],
      '/' => T![/],
      '\\' => T!['\\'],
      '*' => T![*],
      '%' => T![%],
      '#' => T![#],
      ':' => T![:],
      '>' => T![>],
      '<' => T![<],
      'a'..='z' | 'A'..='Z' | '_' => T![ident],
      '0'..='9' => T![integer],

      _ => T![char],
    };
    Ok(t)
  }
}

pub struct Lexer<'a> {
  tok:  Tokenizer<'a>,
  span: Range<usize>,
}

impl<'a> Lexer<'a> {
  pub fn new(input: &'a str) -> Self { Lexer { tok: Tokenizer::new(input), span: 0..0 } }

  fn ok(&mut self, start: usize, tok: SyntaxKind) -> Result<SyntaxKind> {
    self.span.start = start;
    self.span.end = self.tok.pos();
    Ok(tok)
  }

  pub fn eat_whitespace(&mut self) -> Result<Option<SyntaxKind>> {
    match self.tok.peek()? {
      Some(T![ws]) => {
        self.tok.eat().unwrap();
        Ok(Some(T![ws]))
      }
      Some(_) | None => Ok(None),
    }
  }

  #[allow(clippy::should_implement_trait)] // I'm not going to implement Iterator for this.
  pub fn next(&mut self) -> Result<SyntaxKind> {
    let start = self.tok.pos();
    match self.next0() {
      Ok(t) => Ok(t),

      Err(LexError::InvalidChar) => {
        // Skip this character.
        for c in self.tok.source[self.tok.index..].chars().take(1) {
          self.tok.index += c.len_utf8();
        }

        self.span.start = start;
        self.span.end = self.tok.index;

        Err(LexError::InvalidChar)
      }

      Err(LexError::Eof) => Err(LexError::Eof),
    }
  }

  fn next0(&mut self) -> Result<SyntaxKind> {
    let start = self.tok.pos();
    if let Some(t) = self.eat_whitespace()? {
      while self.eat_whitespace().is_ok_and(|o| o.is_some()) {}
      return self.ok(start, t);
    }

    let first = self.tok.eat()?;
    match first {
      // Line comments.
      T![/] if self.tok.peek() == Ok(Some(first)) => {
        self.tok.eat()?;

        loop {
          match self.tok.eat() {
            Err(LexError::Eof) => break,
            Ok(T![nl]) => break,
            Ok(_) => {}
            Err(e) => return Err(e),
          }
        }

        self.ok(start, T![ws])
      }

      // Block comments.
      T![/] if self.tok.peek() == Ok(Some(T![*])) => {
        self.tok.eat()?;

        let mut depth = 1;

        loop {
          match self.tok.eat() {
            // `/*`
            Ok(T![/]) if self.tok.peek() == Ok(Some(T![*])) => {
              depth += 1;
            }

            // `*/`
            Ok(T![*]) if self.tok.peek() == Ok(Some(T![/])) => {
              depth -= 1;
            }

            Ok(_) => {}
            Err(LexError::Eof) => break,
            Err(e) => return Err(e),
          }

          if depth == 0 {
            self.tok.eat()?;
            break;
          }
        }

        self.ok(start, T![ws])
      }

      // Plain identifier.
      T![ident] => {
        while let Ok(t) = self.tok.peek() {
          match t {
            Some(T![ident] | T![integer]) => {}
            Some(_) | None => break,
          }

          self.tok.eat().unwrap();
        }

        let res = self.ok(start, T![ident]);

        res.map(|r| match self.slice() {
          "if" => T![if],
          "else" => T![else],
          "let" => T![let],
          "def" => T![def],
          "true" => T![true],
          "false" => T![false],
          "nil" => T![nil],
          _ => r,
        })
      }

      // Numbers.
      T![integer] => {
        let mut is_float = false;
        loop {
          match self.tok.peek()? {
            Some(T![integer]) => {}
            Some(T![.]) if !is_float => is_float = true,
            Some(_) | None => break,
          }
          self.tok.eat().unwrap();
        }

        self.ok(start, if is_float { T![float] } else { T![integer] })
      }

      // Handled above.
      T![ws] => unreachable!(),

      // Double-wide tokens.
      T![>] | T![<] | T![=] | T![!] | T![-] | T![|] | T![&] => {
        fn double(a: SyntaxKind, b: SyntaxKind) -> Option<SyntaxKind> {
          Some(match (a, b) {
            (T![>], T![=]) => T![>=],
            (T![<], T![=]) => T![<=],
            (T![=], T![=]) => T![==],
            (T![!], T![=]) => T![!=],
            (T![-], T![>]) => T![->],
            (T![|], T![|]) => T![||],
            (T![&], T![&]) => T![&&],
            _ => return None,
          })
        }

        if let Ok(Some(peeked)) = self.tok.peek() {
          if let Some(t) = double(first, peeked) {
            self.tok.eat()?;
            return self.ok(start, t);
          }
        }

        self.ok(start, first)
      }

      s => self.ok(start, s),
    }
  }

  pub fn slice(&self) -> &'a str { &self.tok.source[self.span.clone()] }

  pub fn range(&self) -> Range<usize> { self.span.clone() }
  pub fn view(&self, range: Range<usize>) -> &'a str { &self.tok.source[range] }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn plain_ident() {
    let mut lexer = Lexer::new("abc");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "abc");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    let mut lexer = Lexer::new("abc_foo");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "abc_foo");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    let mut lexer = Lexer::new("abc_++");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "abc_");
    assert_eq!(lexer.next(), Ok(T![+]));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(T![+]));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    let mut lexer = Lexer::new("abc++");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "abc");
    assert_eq!(lexer.next(), Ok(T![+]));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(T![+]));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    let mut lexer = Lexer::new("abc_def_+");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "abc_def_");
    assert_eq!(lexer.next(), Ok(T![+]));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    let mut lexer = Lexer::new("abc_+_def");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "abc_");
    assert_eq!(lexer.next(), Ok(T![+]));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "_def");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn integers() {
    let mut lexer = Lexer::new("123foo");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "123");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "foo");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn floats() {
    let mut lexer = Lexer::new("2.345");
    assert_eq!(lexer.next(), Ok(T![float]));
    assert_eq!(lexer.slice(), "2.345");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn strings() {
    let mut lexer = Lexer::new("\"\"");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    let mut lexer = Lexer::new(r#" "hi" "#);
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "hi");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    let mut lexer = Lexer::new(
      r#" "hello
           world"
      "#,
    );
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "hello");
    assert_eq!(lexer.next(), Ok(T![nl]));
    assert_eq!(lexer.slice(), "\n");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "           ");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "world");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T![nl]));
    assert_eq!(lexer.slice(), "\n");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "      ");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    // Escapes.
    let mut lexer = Lexer::new("\"foo: \\\"\"");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "foo");
    assert_eq!(lexer.next(), Ok(T![:]));
    assert_eq!(lexer.slice(), ":");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T!['\\']));
    assert_eq!(lexer.slice(), "\\");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    let mut lexer = Lexer::new("\"\\\"\"");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T!['\\']));
    assert_eq!(lexer.slice(), "\\");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn format_strings() {
    let mut lexer = Lexer::new(r#" s"hi" "#);
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "s");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "hi");
    assert_eq!(lexer.next(), Ok(T!['"']));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn line_comments() {
    let mut lexer = Lexer::new(
      "3 // hi
       2 + 3",
    );
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "// hi\n");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "       ");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "2");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![+]));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn block_comments() {
    let mut lexer = Lexer::new("3 /* hi */");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "/* hi */");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    // nested block comments
    let mut lexer = Lexer::new("3 /* hi /* foo */ */");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "/* hi /* foo */ */");
    assert_eq!(lexer.next(), Err(LexError::Eof));

    // block comments over multiple lines
    let mut lexer = Lexer::new("3 /* hi \n */ 4");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "/* hi \n */");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "4");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn invalid_chars() {
    let mut lexer = Lexer::new("⊥");
    assert_eq!(lexer.next(), Ok(T![char]));
    assert_eq!(lexer.slice(), "⊥");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn whole_file() {
    let mut lexer = Lexer::new(
      "class Foo {
        def bar(): Int = 2 + 3
      }",
    );
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "class");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "Foo");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T!['{']));
    assert_eq!(lexer.slice(), "{");
    assert_eq!(lexer.next(), Ok(T![nl]));
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "        ");
    assert_eq!(lexer.next(), Ok(T![def]));
    assert_eq!(lexer.slice(), "def");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "bar");
    assert_eq!(lexer.next(), Ok(T!['(']));
    assert_eq!(lexer.slice(), "(");
    assert_eq!(lexer.next(), Ok(T![')']));
    assert_eq!(lexer.slice(), ")");
    assert_eq!(lexer.next(), Ok(T![:]));
    assert_eq!(lexer.slice(), ":");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![ident]));
    assert_eq!(lexer.slice(), "Int");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![=]));
    assert_eq!(lexer.slice(), "=");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "2");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![+]));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(T![integer]));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(T![nl]));
    assert_eq!(lexer.next(), Ok(T![ws]));
    assert_eq!(lexer.slice(), "      ");
    assert_eq!(lexer.next(), Ok(T!['}']));
    assert_eq!(lexer.slice(), "}");
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }

  #[test]
  fn parses_thin_arrow() {
    let mut lexer = Lexer::new("->");
    assert_eq!(lexer.next(), Ok(T![->]));
    assert_eq!(lexer.next(), Err(LexError::Eof));
  }
}
