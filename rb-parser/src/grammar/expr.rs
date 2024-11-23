use crate::{CompletedMarker, Marker, SyntaxKind, T};

use super::*;

pub fn expr(p: &mut Parser) { expr_bp(p, 0, false); }

fn expr_cond(p: &mut Parser) { expr_bp(p, 0, true); }

fn op_bp(t: SyntaxKind) -> Option<(u8, u8)> {
  // test ok
  // 1 + 2 - 3 * 4 / 5 % 0 == 6 != 7 < 8 > 9 <= 10 >= 11 && 12 || 13
  let prec = match t {
    T![||] | T![&&] => 1,
    T![==] | T![!=] | T![<] | T![>] | T![<=] | T![>=] => 1,
    T![+] | T![-] => 2,
    T![*] | T![/] | T![%] => 3,

    _ => return None,
  };

  let is_right_assoc = false;

  if is_right_assoc {
    Some((prec, prec))
  } else {
    Some((prec, prec + 1))
  }
}

fn expr_bp(p: &mut Parser, min_bp: u8, cond: bool) {
  let m = p.start();
  let Some(mut lhs) = atom_expr(p, m) else { return };
  lhs = postfix_expr(p, lhs);

  loop {
    if let Some((l_bp, r_bp)) = op_bp(p.current()) {
      if l_bp < min_bp {
        return;
      }

      let m = lhs.precede(p);

      {
        let m = p.start();
        p.bump(); // eat the operator
        m.complete(p, BINARY_OP);
      }

      expr_bp(p, r_bp, cond);
      lhs = m.complete(p, BINARY_EXPR);
    } else {
      match p.current() {
        T![nl] | T![,] | T![')'] | T![']'] | T!['}'] | EOF => return,
        T!['{'] if cond => return,
        _ => {
          p.error(format!("expected operator, got {}", p.current()));
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
    // 2.345
    T![integer] | T![float] | T![true] | T![false] | T![nil] => {
      p.bump();
      Some(m.complete(p, LITERAL))
    }

    // test ok
    // hello
    T![ident] => {
      p.eat(T![ident]);
      Some(m.complete(p, NAME))
    }

    // test ok
    // print("hello world!")
    T!['"'] => {
      p.bump();

      // TODO: Escapes and such.
      while !p.at(EOF) && !p.at(T!['"']) {
        if p.at(T![#]) && p.peek() == T!['{'] {
          let m = p.start();
          p.eat(T![#]);
          p.eat(T!['{']);
          expr(p);
          p.expect(T!['}']);
          m.complete(p, INTERPOLATION);
        } else {
          p.bump();
        }
      }

      p.eat(T!['"']);
      Some(m.complete(p, STRING))
    }

    // test ok
    // !!false
    // -true
    T![!] | T![-] => {
      {
        let m = p.start();
        p.bump();
        m.complete(p, PREFIX_OP);
      }
      expr(p);
      Some(m.complete(p, PREFIX_EXPR))
    }

    // test ok
    // (2 + 3)
    // -(4 - 5)
    T!['('] => {
      p.eat(T!['(']);
      expr(p);
      p.expect(T![')']);
      Some(m.complete(p, PAREN_EXPR))
    }

    // test ok
    // []
    // [1, 2, 3]
    T!['['] => {
      arg_list(p, T!['['], T![']']);
      Some(m.complete(p, ARRAY_EXPR))
    }

    // test ok
    // {
    //   print("hello")
    //   print("goodbye")
    // }
    T!['{'] => {
      m.abandon(p);
      Some(super::stmt::block(p))
    }

    T![if] => {
      p.eat(T![if]);
      expr_cond(p);

      // test ok
      // if 1 { print("hello") }
      super::stmt::block(p);

      while p.at(T![else]) {
        p.eat(T![else]);

        if p.at(T![if]) {
          p.eat(T![if]);
          // test ok
          // if 1 { print("hello") } else if 2 { print("bye") }
          // if 1 { print("hello") } else if 2 { print("bye") } else { print("ok") }
          expr_cond(p);
          super::stmt::block(p);
        } else {
          // test ok
          // if 1 { print("hello") } else { print("bye") }
          super::stmt::block(p);
          break;
        }
      }

      Some(m.complete(p, IF_EXPR))
    }

    _ => {
      m.abandon(p);
      p.error(format!("expected expression, got {}", p.current()));

      // Advance to avoid infinite loop.
      p.bump();

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
        arg_list(p, T!['('], T![')']);
        m.complete(p, ARG_LIST);

        call.complete(p, CALL_EXPR)
      }

      _ => break,
    };
  }
  lhs
}

fn arg_list(p: &mut Parser, open: SyntaxKind, close: SyntaxKind) {
  p.eat(open);

  while !p.at(EOF) && !p.at(close) {
    // test ok
    // foo(
    //   2)
    while p.at(T![nl]) {
      p.eat(T![nl]);
    }

    expr(p);

    // test ok
    // foo(
    //   2
    //   ,
    //   3
    // )
    while p.at(T![nl]) {
      p.eat(T![nl]);
    }

    if p.at(T![,]) {
      p.eat(T![,]);

      // test ok
      // foo(2
      // )
      // foo(
      //   2
      // )
      while p.at(T![nl]) {
        p.eat(T![nl]);
      }
      if p.at(close) {
        break;
      }
    } else {
      break;
    }
  }

  p.expect(close);
}

#[cfg(test)]
mod tests {
  use crate::tests::{check, check_expr};

  #[test]
  fn it_works() {
    check(
      r#"
        print("hello world!")
        print(2 + 3)
      "#,
      expect![@r#"
        SOURCE_FILE
          NL_KW '\n'
          WHITESPACE '        '
          EXPR_STMT
            CALL_EXPR
              NAME
                IDENT 'print'
              ARG_LIST
                OPEN_PAREN '('
                STRING
                  DOUBLE_QUOTE '"'
                  IDENT 'hello'
                  WHITESPACE ' '
                  IDENT 'world'
                  BANG '!'
                  DOUBLE_QUOTE '"'
                CLOSE_PAREN ')'
          NL_KW '\n'
          WHITESPACE '        '
          EXPR_STMT
            CALL_EXPR
              NAME
                IDENT 'print'
              ARG_LIST
                OPEN_PAREN '('
                BINARY_EXPR
                  LITERAL
                    INTEGER_KW '2'
                  WHITESPACE ' '
                  BINARY_OP
                    PLUS '+'
                  WHITESPACE ' '
                  LITERAL
                    INTEGER_KW '3'
                CLOSE_PAREN ')'
          NL_KW '\n'
          WHITESPACE '      '
      "#],
    );
  }

  #[test]
  fn literals() {
    check_expr(
      "1",
      expect![@r#"
        LITERAL
          INTEGER_KW '1'
      "#],
    );

    check_expr(
      "2.234",
      expect![@r#"
        LITERAL
          FLOAT_KW '2.234'
      "#],
    );

    check_expr(
      "true",
      expect![@r#"
        LITERAL
          TRUE_KW 'true'
      "#],
    );

    check_expr(
      "false",
      expect![@r#"
        LITERAL
          FALSE_KW 'false'
      "#],
    );

    check_expr(
      "nil",
      expect![@r#"
        LITERAL
          NIL_KW 'nil'
      "#],
    );
  }

  #[test]
  fn string_interpolation() {
    check(
      r#"
        "hello #{world}"
      "#,
      expect![@r#"
        SOURCE_FILE
          NL_KW '\n'
          WHITESPACE '        '
          EXPR_STMT
            STRING
              DOUBLE_QUOTE '"'
              IDENT 'hello'
              WHITESPACE ' '
              INTERPOLATION
                POUND '#'
                OPEN_CURLY '{'
                NAME
                  IDENT 'world'
                CLOSE_CURLY '}'
              DOUBLE_QUOTE '"'
          NL_KW '\n'
          WHITESPACE '      '
      "#],
    );
  }
}
