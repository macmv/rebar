use crate::{Parser, SyntaxKind::*, T};

pub fn stmt(p: &mut Parser) {
  match p.current() {
    T![def] => {
      let m = p.start();
      p.eat(T![def]);
      p.expect(T![ident]);

      params(p);

      if p.at(T![nl]) {
        p.bump();
      } else {
        p.error("expected newline");
      }

      while !p.at(T!['}']) {
        stmt(p);
      }

      p.bump();
    }

    _ => super::expr::expr(p),
  }

  // test err
  // foo bar
  if p.current() != T![nl] {
    p.error("expected end of statement");
  }
  while p.current() != T![nl] {
    p.bump();
  }
  p.eat(T![nl]);
}

fn params(p: &mut Parser) {
  p.expect(T!['(']);

  while !p.at(EOF) && !p.at(T![')']) {
    p.expect(T![ident]);
    p.expect(T![:]);
    super::types::ty(p);

    if p.at(T![,]) {
      p.bump();
      if p.at(T![')']) {
        break;
      }
    } else {
      break;
    }
  }

  p.expect(T![')']);
}
