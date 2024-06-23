use crate::{Parser, SyntaxKind::*, T};

pub fn block(p: &mut Parser) {
  let m = p.start();
  p.expect(T!['{']);

  while !p.at(EOF) && !p.at(T!['}']) {
    stmt(p);
  }

  p.expect(T!['}']);
  m.complete(p, BLOCK);
}

pub fn stmt(p: &mut Parser) {
  while p.at(T![nl]) {
    p.eat(T![nl]);
  }

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

    _ => {
      let m = p.start();
      super::expr::expr(p);
      m.complete(p, EXPR_STMT);
    }
  }

  match p.current() {
    T![nl] => p.eat(T![nl]),
    T!['}'] => {}
    _ => {
      // test err
      // foo bar
      p.error("expected end of statement");

      while !p.at(EOF) && !p.at(T![nl]) && !p.at(T!['}']) {
        p.bump();
      }

      match p.current() {
        T![nl] => p.eat(T![nl]),
        T!['}'] => {}
        _ => {}
      }
    }
  }
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
