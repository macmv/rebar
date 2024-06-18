use crate::{Parser, T};

pub fn ty(p: &mut Parser) {
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
}
