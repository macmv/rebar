use crate::{Parser, SyntaxKind::*, T};

pub fn ty(p: &mut Parser) {
  let m = p.start();

  match p.current() {
    T![ident] => {
      p.bump();
    }

    T!['('] => {
      p.bump();
      ty(p);
      p.expect(T![')']);
    }

    _ => p.error("expected type"),
  }

  m.complete(p, TYPE);
}
