use crate::{CompletedMarker, Marker, T};

use super::*;

pub fn expr(p: &mut Parser) { let _ = expr0(p); }

fn expr0(p: &mut Parser) -> Option<CompletedMarker> {
  let m = p.start();
  let lhs = atom_expr(p, m)?;
  let _m = postfix_expr(p, lhs);

  None
}

fn atom_expr(p: &mut Parser, m: Marker) -> Option<CompletedMarker> {
  match p.current() {
    // test ok
    // 2.345
    t @ (T![ident] | T![integer] | T![float]) => {
      p.bump();
      Some(m.complete(p, t))
    }

    _ => {
      m.abandon(p);
      p.error(format!("expected expression, got {:?}", p.current()));
      None
    }
  }
}

fn postfix_expr(p: &mut Parser, mut lhs: CompletedMarker) -> CompletedMarker {
  loop {
    lhs = match p.current() {
      // test ok
      // hi(3)
      T!['('] => {
        let call = lhs.precede(p);

        let m = p.start();
        paren_args(p);
        m.complete(p, PAREN_ARGS);

        call.complete(p, CALL_EXPR)
      }

      _ => break,
    };
  }
  lhs
}

fn paren_args(p: &mut Parser) {
  p.eat(T!['(']);

  while !p.at(EOF) && !p.at(T![')']) {
    expr(p);
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
