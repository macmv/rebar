use crate::{Parser, SyntaxKind::*, T};

pub fn ty(p: &mut Parser) {
  let m = p.start();

  match p.current() {
    // test ok
    // def foo(a: int) {}
    // def foo(a: nil) {}
    T![ident] | T![nil] => {
      p.bump();
    }

    T!['('] => {
      p.bump();
      ty(p);
      p.expect(T![')']);
    }

    _ => p.error("expected type"),
  }

  // test ok
  // def foo(a: int | nil) {}
  match p.current() {
    T![|] => {
      p.bump();
      ty(p);
    }

    _ => (),
  }

  m.complete(p, TYPE);
}
