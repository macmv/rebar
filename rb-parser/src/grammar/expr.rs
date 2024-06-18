use crate::{CompletedMarker, Marker, SyntaxKind, T};

use super::*;

pub fn expr(p: &mut Parser) { expr_bp(p, 0); }

fn op_bp(t: SyntaxKind) -> Option<(u8, u8)> {
  // test ok
  // 1 + 2 - 3 * 4 / 5
  let prec = match t {
    T![+] | T![-] => 1,
    T![*] | T![/] => 2,

    _ => return None,
  };

  let is_right_assoc = false;

  if is_right_assoc {
    Some((prec, prec))
  } else {
    Some((prec, prec + 1))
  }
}

fn expr_bp(p: &mut Parser, min_bp: u8) {
  let m = p.start();
  let Some(mut lhs) = atom_expr(p, m) else { return };
  lhs = postfix_expr(p, lhs);

  loop {
    if let Some((l_bp, r_bp)) = op_bp(p.current()) {
      if l_bp < min_bp {
        return;
      }

      let m = lhs.precede(p);
      p.bump(); // eat the operator

      expr_bp(p, r_bp);
      lhs = m.complete(p, BINARY_EXPR);
    } else {
      match p.current() {
        T![nl] | T![,] | T![')'] | T!['}'] => return,
        _ => {
          p.error(format!("expected operator, got {:?}", p.current()));
          return;
        }
      }
    }
  }
}

fn atom_expr(p: &mut Parser, m: Marker) -> Option<CompletedMarker> {
  match p.current() {
    // test ok
    // 2
    // hello
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
      // hello(2, 3)(4)
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
