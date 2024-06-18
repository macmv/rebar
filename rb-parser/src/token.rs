use std::ops::Range;

use thiserror::Error;

// Scala's grammar is quite finicky. We expose a `Token` enum that is a
// parser-usable version of a token. It contains high level concepts like
// "Identifiers" and "Numbers".
//
// In order to actually parse identifiers (of all things), we have a separate
// inner token type, which implements the various parts of an identifier.

#[derive(Debug, PartialEq)]
pub enum Token {
  Ident,
  Literal(Literal),

  Group(Group),
  Delimiter(Delimiter),
  Newline,
  Whitespace,

  Invalid,
}

#[derive(Debug, PartialEq)]
pub enum Literal {
  Integer,
  Float,
}

pub type Result<T> = std::result::Result<T, LexError>;

#[derive(Debug, Error, PartialEq)]
pub enum LexError {
  #[error("invalid character")]
  InvalidChar,

  #[error("end of file reached")]
  EOF,
}

// Below we have the lexer internals.

#[derive(Clone, Copy, Debug, PartialEq)]
enum InnerToken {
  Whitespace,
  Newline,

  Underscore,
  Letter,
  Digit,

  Group(Group),
  Delimiter(Delimiter),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Group {
  OpenParen,
  CloseParen,

  OpenBracket,
  CloseBracket,

  OpenBrace,
  CloseBrace,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Delimiter {
  SingleQuote,
  DoubleQuote,
  Dot,
  Comma,
  Colon,
  Equals,

  Plus,
  Minus,
  Star,
  Slash,
  Backslash,
}

struct Tokenizer<'a> {
  source: &'a str,
  index:  usize,
}

impl<'a> Tokenizer<'a> {
  pub fn new(source: &'a str) -> Self { Tokenizer { source, index: 0 } }

  pub fn pos(&self) -> usize { self.index }

  pub fn peek(&mut self) -> Result<Option<InnerToken>> {
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

  pub fn eat(&mut self) -> Result<InnerToken> {
    let Some(c) = self.source[self.index..].chars().next() else {
      return Err(LexError::EOF);
    };
    self.index += c.len_utf8();
    let t = match c {
      '\u{0020}' | '\u{0009}' | '\u{000d}' => InnerToken::Whitespace,
      '\n' => InnerToken::Newline,

      '(' => InnerToken::Group(Group::OpenParen),
      ')' => InnerToken::Group(Group::CloseParen),
      '[' => InnerToken::Group(Group::OpenBracket),
      ']' => InnerToken::Group(Group::CloseBracket),
      '{' => InnerToken::Group(Group::OpenBrace),
      '}' => InnerToken::Group(Group::CloseBrace),

      '+' => InnerToken::Delimiter(Delimiter::Plus),
      '-' => InnerToken::Delimiter(Delimiter::Minus),
      '=' => InnerToken::Delimiter(Delimiter::Equals),
      '\'' => InnerToken::Delimiter(Delimiter::SingleQuote),
      '"' => InnerToken::Delimiter(Delimiter::DoubleQuote),
      '.' => InnerToken::Delimiter(Delimiter::Dot),
      ',' => InnerToken::Delimiter(Delimiter::Comma),
      '/' => InnerToken::Delimiter(Delimiter::Slash),
      '\\' => InnerToken::Delimiter(Delimiter::Backslash),
      '*' => InnerToken::Delimiter(Delimiter::Star),
      ':' => InnerToken::Delimiter(Delimiter::Colon),

      '_' => InnerToken::Underscore,
      'a'..='z' | 'A'..='Z' => InnerToken::Letter,
      '0'..='9' => InnerToken::Digit,

      _ => return Err(LexError::InvalidChar),
    };
    Ok(t)
  }

  pub fn span(&self) -> Range<usize> { self.index - 1..self.index }
}

pub struct Lexer<'a> {
  tok:  Tokenizer<'a>,
  span: Range<usize>,
}

impl<'a> Lexer<'a> {
  pub fn new(input: &'a str) -> Self { Lexer { tok: Tokenizer::new(input), span: 0..0 } }

  fn ok(&mut self, start: usize, tok: Token) -> Result<Token> {
    self.span.start = start;
    self.span.end = self.tok.span().end;
    Ok(tok)
  }

  pub fn eat_whitespace(&mut self) -> Result<Option<Token>> {
    loop {
      match self.tok.peek()? {
        Some(InnerToken::Whitespace) => {
          self.tok.eat().unwrap();
          return Ok(Some(Token::Whitespace));
        }
        Some(_) | None => break,
      }
    }
    Ok(None)
  }

  pub fn next(&mut self) -> Result<Token> {
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

      Err(LexError::EOF) => Err(LexError::EOF),
    }
  }

  fn next0(&mut self) -> Result<Token> {
    let start = self.tok.pos();
    if let Some(t) = self.eat_whitespace()? {
      while self.eat_whitespace().is_ok_and(|o| o.is_some()) {}
      return self.ok(start, t);
    }

    let first = self.tok.eat()?;
    match first {
      // Line comments.
      InnerToken::Delimiter(Delimiter::Slash) if self.tok.peek() == Ok(Some(first)) => {
        self.tok.eat()?;

        loop {
          match self.tok.eat() {
            Err(LexError::EOF) => break,
            Ok(InnerToken::Newline) => break,
            Ok(_) => {}
            Err(e) => return Err(e),
          }
        }

        self.ok(start, Token::Whitespace)
      }

      // Block comments.
      InnerToken::Delimiter(Delimiter::Slash)
        if self.tok.peek() == Ok(Some(InnerToken::Delimiter(Delimiter::Star))) =>
      {
        self.tok.eat()?;

        let mut depth = 1;

        loop {
          match self.tok.eat() {
            // `/*`
            Ok(InnerToken::Delimiter(Delimiter::Slash))
              if self.tok.peek() == Ok(Some(InnerToken::Delimiter(Delimiter::Star))) =>
            {
              depth += 1;
            }

            // `*/`
            Ok(InnerToken::Delimiter(Delimiter::Star))
              if self.tok.peek() == Ok(Some(InnerToken::Delimiter(Delimiter::Slash))) =>
            {
              depth -= 1;
            }

            Ok(_) => {}
            Err(LexError::EOF) => break,
            Err(e) => return Err(e),
          }

          if depth == 0 {
            self.tok.eat()?;
            break;
          }
        }

        self.ok(start, Token::Whitespace)
      }

      // Plain identifier.
      InnerToken::Underscore | InnerToken::Letter => {
        while let Ok(t) = self.tok.peek() {
          match t {
            Some(InnerToken::Letter | InnerToken::Digit | InnerToken::Underscore) => {}
            Some(_) | None => break,
          }

          self.tok.eat().unwrap();
        }

        self.ok(start, Token::Ident)
      }

      // Numbers.
      InnerToken::Digit => {
        let mut is_float = false;
        loop {
          match self.tok.peek()? {
            Some(InnerToken::Digit) => {}
            Some(InnerToken::Delimiter(Delimiter::Dot)) if !is_float => is_float = true,
            Some(_) | None => break,
          }
          self.tok.eat().unwrap();
        }

        self.ok(start, Token::Literal(if is_float { Literal::Float } else { Literal::Integer }))
      }

      InnerToken::Delimiter(d) => self.ok(start, Token::Delimiter(d)),
      InnerToken::Group(g) => self.ok(start, Token::Group(g)),
      InnerToken::Newline => self.ok(start, Token::Newline),

      // Handled above.
      InnerToken::Whitespace => unreachable!(),
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
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "abc");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    let mut lexer = Lexer::new("abc_foo");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "abc_foo");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    let mut lexer = Lexer::new("abc_++");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "abc_");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Plus)));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Plus)));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    let mut lexer = Lexer::new("abc++");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "abc");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Plus)));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Plus)));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    let mut lexer = Lexer::new("abc_def_+");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "abc_def_");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Plus)));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    let mut lexer = Lexer::new("abc_+_def");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "abc_");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Plus)));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "_def");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }

  #[test]
  fn integers() {
    let mut lexer = Lexer::new("123foo");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "123");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "foo");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }

  #[test]
  fn floats() {
    let mut lexer = Lexer::new("2.345");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Float)));
    assert_eq!(lexer.slice(), "2.345");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }

  #[test]
  fn strings() {
    let mut lexer = Lexer::new("\"\"");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    let mut lexer = Lexer::new(r#" "hi" "#);
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "hi");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    let mut lexer = Lexer::new(
      r#" "hello
           world"
      "#,
    );
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "hello");
    assert_eq!(lexer.next(), Ok(Token::Newline));
    assert_eq!(lexer.slice(), "\n");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "           ");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "world");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Newline));
    assert_eq!(lexer.slice(), "\n");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "      ");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    // Escapes.
    let mut lexer = Lexer::new("\"foo: \\\"\"");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "foo");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Colon)));
    assert_eq!(lexer.slice(), ":");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Backslash)));
    assert_eq!(lexer.slice(), "\\");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    let mut lexer = Lexer::new("\"\\\"\"");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Backslash)));
    assert_eq!(lexer.slice(), "\\");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }

  #[test]
  fn format_strings() {
    let mut lexer = Lexer::new(r#" s"hi" "#);
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "s");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "hi");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::DoubleQuote)));
    assert_eq!(lexer.slice(), "\"");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }

  #[test]
  fn line_comments() {
    let mut lexer = Lexer::new(
      "3 // hi
       2 + 3",
    );
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "// hi\n");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "       ");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "2");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Plus)));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }

  #[test]
  fn block_comments() {
    let mut lexer = Lexer::new("3 /* hi */");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "/* hi */");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    // nested block comments
    let mut lexer = Lexer::new("3 /* hi /* foo */ */");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "/* hi /* foo */ */");
    assert_eq!(lexer.next(), Err(LexError::EOF));

    // block comments over multiple lines
    let mut lexer = Lexer::new("3 /* hi \n */ 4");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "/* hi \n */");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "4");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }

  #[test]
  fn invalid_chars() {
    let mut lexer = Lexer::new("⊥");
    assert_eq!(lexer.next(), Err(LexError::InvalidChar));
    assert_eq!(lexer.slice(), "⊥");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }

  #[test]
  fn whole_file() {
    let mut lexer = Lexer::new(
      "class Foo {
        def bar(): Int = 2 + 3
      }",
    );
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "class");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "Foo");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Group(Group::OpenBrace)));
    assert_eq!(lexer.slice(), "{");
    assert_eq!(lexer.next(), Ok(Token::Newline));
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "        ");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "def");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "bar");
    assert_eq!(lexer.next(), Ok(Token::Group(Group::OpenParen)));
    assert_eq!(lexer.slice(), "(");
    assert_eq!(lexer.next(), Ok(Token::Group(Group::CloseParen)));
    assert_eq!(lexer.slice(), ")");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Colon)));
    assert_eq!(lexer.slice(), ":");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Ident));
    assert_eq!(lexer.slice(), "Int");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Equals)));
    assert_eq!(lexer.slice(), "=");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "2");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Delimiter(Delimiter::Plus)));
    assert_eq!(lexer.slice(), "+");
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), " ");
    assert_eq!(lexer.next(), Ok(Token::Literal(Literal::Integer)));
    assert_eq!(lexer.slice(), "3");
    assert_eq!(lexer.next(), Ok(Token::Newline));
    assert_eq!(lexer.next(), Ok(Token::Whitespace));
    assert_eq!(lexer.slice(), "      ");
    assert_eq!(lexer.next(), Ok(Token::Group(Group::CloseBrace)));
    assert_eq!(lexer.slice(), "}");
    assert_eq!(lexer.next(), Err(LexError::EOF));
  }
}
