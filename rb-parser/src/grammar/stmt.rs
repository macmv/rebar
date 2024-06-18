use crate::{Parser, SyntaxKind::*, T};

pub fn stmt(p: &mut Parser) {
  match p.current() {
    // test ok
    // def foo(bar: int, baz: float) -> string
    T![def] => {
      let m = p.start();
      p.eat(T![def]);
      p.expect(T![ident]);

      params(p);

      m.complete(p, DEF);
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

  if p.at(T![->]) {
    p.eat(T![->]);
    super::types::ty(p);
  }
}
