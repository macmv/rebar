use crate::fmt::{format_opts, Formatter};
use rb_syntax::cst;
use rb_test::{expect, Expect};

fn check(input: &str, expected: Expect) {
  let input = input.strip_prefix('\n').unwrap();

  let cst = cst::SourceFile::parse(input);
  for error in cst.errors() {
    panic!("{}", error.message());
  }

  expected
    .assert_eq(&format_opts(&cst.tree(), Formatter { max_line_length: 30, ..Default::default() }));
}

#[test]
fn it_works() {
  check(
    r#"
      print_impl  (  2   *   3+4+5)
    "#,
    expect![@r#"
      print_impl(2 * 3 + 4 + 5)
    "#],
  );
}

#[test]
fn call_singleline() {
  check(
    r#"
      print_impl(2+3,   4*5)
    "#,
    expect![@r#"
      print_impl(2 + 3, 4 * 5)
    "#],
  );

  check(
    r#"
      print_impl(2,3,)
    "#,
    expect![@r#"
      print_impl(2, 3)
    "#],
  );

  check(
    r#"
      print_impl(
        2,
        3,
      )
    "#,
    expect![@r#"
      print_impl(2, 3)
    "#],
  );
}

#[test]
fn call_multline() {
  check(
    r#"
      print_impl(very_long_arg_1, very_long_arg_2)
    "#,
    expect![@r#"
      print_impl(
        very_long_arg_1,
        very_long_arg_2,
      )
    "#],
  );
  check(
    r#"
      print_impl(
        very_long_arg_1,
        very_long_arg_2,
      )
    "#,
    expect![@r#"
      print_impl(
        very_long_arg_1,
        very_long_arg_2,
      )
    "#],
  );
}

#[test]
fn keep_line_comment() {
  check(
    r#"
      // hello
      print(1, 2)
    "#,
    expect![@r#"
      // hello
      print(1, 2)
    "#],
  );
}

#[test]
fn keep_trailing_comment() {
  check(
    r#"
      print(1, 2)
      // hello
    "#,
    expect![@r#"
      print(1, 2)
      // hello
    "#],
  );
}

#[test]
fn keep_empty_line() {
  check(
    r#"
      print(1)
      print(2)
    "#,
    expect![@r#"
      print(1)
      print(2)
    "#],
  );

  check(
    r#"
      print(1)

      print(2)
    "#,
    expect![@r#"
      print(1)

      print(2)
    "#],
  );

  check(
    r#"
      print(1)


      print(2)
    "#,
    expect![@r#"
      print(1)

      print(2)
    "#],
  );

  check(
    r#"
      print(1)



      print(2)
    "#,
    expect![@r#"
      print(1)

      print(2)
    "#],
  );
}

#[test]
fn keep_empty_lines_comments() {
  check(
    r#"
      // hello
      print(2)
    "#,
    expect![@r#"
      // hello
      print(2)
    "#],
  );

  check(
    r#"
      // hello

      print(2)
    "#,
    expect![@r#"
      // hello

      print(2)
    "#],
  );

  check(
    r#"
      // hello


      print(2)
    "#,
    expect![@r#"
      // hello

      print(2)
    "#],
  );

  check(
    r#"
      // hello



      print(2)
    "#,
    expect![@r#"
      // hello

      print(2)
    "#],
  );

  check(
    r#"
      print(1)


      // hello


      print(2)
    "#,
    expect![@r#"
      print(1)

      // hello

      print(2)
    "#],
  );
}

#[test]
fn no_leading_whitespace() {
  check(
    &r#"
      // hi
      print(1)
    "#
    .lines()
    .map(|line| line.trim())
    .collect::<Vec<_>>()
    .join("\n"),
    expect![@r#"
      // hi
      print(1)
    "#],
  );

  check(
    &r#"
      assert_eq(2 + 3, 5)

      // precedence should work
      assert_eq(2 * 3 + 4, 10)
      assert_eq(4 + 2 * 3, 10)
    "#
    .lines()
    .map(|line| line.trim())
    .collect::<Vec<_>>()
    .join("\n"),
    expect![@r#"
      assert_eq(2 + 3, 5)

      // precedence should work
      assert_eq(2 * 3 + 4, 10)
      assert_eq(4 + 2 * 3, 10)
    "#],
  );
}

#[test]
fn handle_trailing_newlines() {
  check(
    &r#"
      assert_eq(2 + 3, 5)

      // precedence should work
      assert_eq(2 * 3 + 4, 10)
      assert_eq(4 + 2 * 3, 10)

    "#
    .lines()
    .map(|line| line.trim())
    .collect::<Vec<_>>()
    .join("\n"),
    expect![@r#"
      assert_eq(2 + 3, 5)

      // precedence should work
      assert_eq(2 * 3 + 4, 10)
      assert_eq(4 + 2 * 3, 10)
    "#],
  );

  check(
    &r#"
      assert_eq(2 + 3, 5)

      // precedence should work
      assert_eq(2 * 3 + 4, 10)
      assert_eq(4 + 2 * 3, 10)

    "#,
    expect![@r#"
      assert_eq(2 + 3, 5)

      // precedence should work
      assert_eq(2 * 3 + 4, 10)
      assert_eq(4 + 2 * 3, 10)
    "#],
  );
}

#[test]
fn let_stmt() {
  check(
    &r#"
      let   foo   =   3
    "#,
    expect![@r#"
      let foo = 3
    "#],
  );
}

#[test]
fn if_stmt() {
  check(
    &r#"
      if  0  {
        println(2  +  3)
      }  else  {
        println(4  +  5)
      }
    "#,
    expect![@r#"
      if 0 {
        println(2 + 3)
      } else {
        println(4 + 5)
      }
    "#],
  );

  check(
    &r#"
      if  0  {
        println(2)
        println(3)
      }  else  {
        println(4)
        println(5)
      }
    "#,
    expect![@r#"
      if 0 {
        println(2)
        println(3)
      } else {
        println(4)
        println(5)
      }
    "#],
  );
}

#[test]
fn long_binary_op() {
  check(
    &r#"
      fooooooooooooooooooooooooooooooooooo + baaaaaaaaaaaaaaaaaar
    "#,
    expect![@r#"
      fooooooooooooooooooooooooooooooooooo
        + baaaaaaaaaaaaaaaaaar
    "#],
  );

  check(
    &r#"
      1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10
    "#,
    expect![@r#"
      1 + 2 + 3 + 4 + 5 + 6 + 7 + 8
        + 9 + 10
    "#],
  );
}

#[test]
fn def_stmt() {
  check(
    &r#"
      def  foo  (  x : int ,  y : str )  {
        x  +  y
      }
    "#,
    expect![@r#"
      def foo(x: int, y: str) { x
        + y }
    "#],
  );

  check(
    &r#"
      def foo(x:int,y:str){x+y}
    "#,
    expect![@r#"
      def foo(x: int, y: str) { x
        + y }
    "#],
  );
}

#[test]
fn blocks() {
  check(
    r#"
      {
         let  x  =  2  +  3
         let  y  =  4
      }
    "#,
    expect![@r#"
      {
        let x = 2 + 3
        let y = 4
      }
    "#],
  );
}

#[test]
fn strings() {
  check(
    r#"
      assert_eq (  "  h  "  ,  "  h  "  )
    "#,
    expect![@r#"
      assert_eq("  h  ", "  h  ")
    "#],
  );
}

#[test]
fn interpolated_string() {
  check(
    r#"
      "hello #{  2  +  3  }"
    "#,
    expect![@r#"
      "hello #{2 + 3}"
    "#],
  );
}

#[test]
fn arrays() {
  check(
    r#"
      [  ]
    "#,
    expect![@r#"
      []
    "#],
  );

  check(
    r#"
      [  1  ,  2  ,  3  ]
    "#,
    expect![@r#"
      [1, 2, 3]
    "#],
  );
}

#[test]
fn nested_multiline_array() {
  check(
    r#"
      let a = {
        let b = [1,
        2]
        b
      }
    "#,
    expect![@r#"
      let a = {
        let b = [1, 2]
        b
      }
    "#],
  );
}

#[test]
fn nested_multiline_call() {
  check(
    r#"
      assert_eq({
          1
          2
        }, 2)
    "#,
    expect![@r#"
      assert_eq(
        {
          1
          2
        },
        2,
      )
    "#],
  );

  check(
    r#"
      assert_eq({{
          1
          2
        }}, 2)
    "#,
    expect![@r#"
      assert_eq(
        {
          {
            1
            2
          }
        },
        2,
      )
    "#],
  );
}

#[test]
fn nested_multiline_if() {
  check(
    r#"
      assert_eq(if true {
          1
          2
        } else { 3 }, 2)
    "#,
    expect![@r#"
      assert_eq(
        if true {
          1
          2
        } else {
          3
        },
        2,
      )
    "#],
  );
}
