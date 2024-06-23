//! This module generates AST datatype used by rebar. It is _heavily_ inspired
//! from rust-analyzer's:
//! https://github.com/rust-lang/rust-analyzer/blob/e4344f5fce3b4ca12d51bf27b9a0bd29297be3ea/crates/syntax/src/tests/sourcegen_ast.rs.
//!
//! Specifically, it generates the `SyntaxKind` enum and a number of newtype
//! wrappers around `SyntaxNode` which implement `syntax::AstNode`.

use std::{collections::BTreeSet, fmt::Write};

use itertools::Itertools;
use proc_macro2::{Ident, Punct, Spacing, Span, TokenStream};
use quote::{format_ident, quote};
use ungrammar::{Grammar, Rule};

use super::{
  ast_src::{AstEnumSrc, AstNodeSrc, AstSrc, Cardinality, Field},
  sourcegen,
};

pub fn sourcegen_kinds() {
  let grammar: Grammar =
    include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/rebar.ungram")).parse().unwrap();
  let ast = lower(&grammar);

  let syntax_kinds = generate_syntax_kinds(&ast);
  let syntax_kinds_file = sourcegen::project_root().join("rb-parser/src/syntax_kind/generated.rs");
  sourcegen::ensure_file_contents(syntax_kinds_file.as_path(), &syntax_kinds);
}

pub fn sourcegen_ast() {
  let grammar = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/rebar.ungram")).parse().unwrap();
  let ast = lower(&grammar);

  let ast_tokens = generate_tokens(&ast);
  let ast_tokens_file = sourcegen::project_root().join("rb-syntax/src/generated/tokens.rs");
  sourcegen::ensure_file_contents(ast_tokens_file.as_path(), &ast_tokens);

  let ast_nodes = generate_nodes(&ast);
  let ast_nodes_file = sourcegen::project_root().join("rb-syntax/src/generated/nodes.rs");
  sourcegen::ensure_file_contents(ast_nodes_file.as_path(), &ast_nodes);
}

fn generate_tokens(grammar: &AstSrc) -> String {
  // TODO: Need to re-add these tokens.
  let tokens = grammar.tokens.iter().map(|token| {
    let name = format_ident!("{}", token);
    let kind = format_ident!("{}", to_upper_snake_case(token));
    quote! {
      #[derive(Debug, Clone, PartialEq, Eq, Hash)]
      pub struct #name {
        pub(crate) syntax: SyntaxToken,
      }
      impl std::fmt::Display for #name {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
          std::fmt::Display::fmt(&self.syntax, f)
        }
      }
      impl AstToken for #name {
        fn can_cast(kind: SyntaxKind) -> bool { kind == #kind }
        fn cast(syntax: SyntaxToken) -> Option<Self> {
          if Self::can_cast(syntax.kind()) { Some(Self { syntax }) } else { None }
        }
        fn syntax(&self) -> &SyntaxToken { &self.syntax }
      }
    }
  });

  sourcegen::add_preamble(
    "sourcegen_ast",
    sourcegen::reformat(
      quote! {
        use crate::{ext::AstToken, node::SyntaxToken};
        use rb_parser::SyntaxKind::{self, *};

        #(#tokens)*
      }
      .to_string(),
    ),
  )
  .replace("#[derive", "\n#[derive")
}

fn generate_nodes(grammar: &AstSrc) -> String {
  let (node_defs, node_boilerplate_impls): (Vec<_>, Vec<_>) = grammar
    .nodes
    .iter()
    .map(|node| {
      let name = format_ident!("{}", node.name);
      let kind = format_ident!("{}", to_upper_snake_case(&node.name));
      let traits = node
        .traits
        .iter()
        .filter(|trait_name| {
          // Loops have two expressions so this might collide, therefor manual impl it
          node.name != "ForExpr" && node.name != "WhileExpr" || trait_name.as_str() != "HasLoopBody"
        })
        .map(|trait_name| {
          let trait_name = format_ident!("{}", trait_name);
          quote!(impl ast::#trait_name for #name {})
        });

      let methods = node.fields.iter().map(|field| {
        let method_name = field.method_name();
        let ty = field.ty();

        if let Some(token_kind) = field.token_kind() {
          if field.is_many() {
            quote! {
              pub fn #method_name(&self) -> AstTokenChildren {
                support::token_children(&self.syntax, #token_kind)
              }
            }
          } else {
            quote! {
              pub fn #method_name(&self) -> Option<#ty> {
                support::token(&self.syntax, #token_kind)
              }
            }
          }
        } else if field.is_many() {
          quote! {
            pub fn #method_name(&self) -> AstChildren<#ty> {
              support::children(&self.syntax)
            }
          }
        } else {
          quote! {
            pub fn #method_name(&self) -> Option<#ty> {
              support::child(&self.syntax)
            }
          }
        }
      });
      (
        quote! {
          #[pretty_doc_comment_placeholder_workaround]
          #[derive(Debug, Clone, PartialEq, Eq, Hash)]
          pub struct #name {
            pub(crate) syntax: SyntaxNode,
          }

          #(#traits)*

          impl #name {
            #(#methods)*
          }
        },
        quote! {
          impl AstNode for #name {
            fn can_cast(kind: SyntaxKind) -> bool {
              kind == #kind
            }
            fn cast(syntax: SyntaxNode) -> Option<Self> {
              if Self::can_cast(syntax.kind()) { Some(Self { syntax }) } else { None }
            }
            fn syntax(&self) -> &SyntaxNode { &self.syntax }
          }
        },
      )
    })
    .unzip();

  let (enum_defs, enum_boilerplate_impls): (Vec<_>, Vec<_>) = grammar
    .enums
    .iter()
    .map(|en| {
      let variants: Vec<_> = en.variants.iter().map(|var| format_ident!("{}", var)).collect();
      let name = format_ident!("{}", en.name);
      let kinds: Vec<_> = variants
        .iter()
        .map(|name| format_ident!("{}", to_upper_snake_case(&name.to_string())))
        .collect();

      // Check for enums in enums, which is disallowed.

      for name in en.variants.iter() {
        if grammar.enums.iter().any(|e| &e.name == name) {
          panic!("enums cannot store enums: {} in {}", name, en.name);
        }
      }

      let traits = en.traits.iter().map(|trait_name| {
        let trait_name = format_ident!("{}", trait_name);
        quote!(impl ast::#trait_name for #name {})
      });

      let ast_node = quote! {
        impl AstNode for #name {
          fn can_cast(kind: SyntaxKind) -> bool {
            matches!(kind, #(#kinds)|*)
          }
          fn cast(syntax: SyntaxNode) -> Option<Self> {
            let res = match syntax.kind() {
              #(
              #kinds => #name::#variants(#variants { syntax }),
              )*
              _ => return None,
            };
            Some(res)
          }
          fn syntax(&self) -> &SyntaxNode {
            match self {
              #(
              #name::#variants(it) => &it.syntax,
              )*
            }
          }
        }
      };

      (
        quote! {
          #[pretty_doc_comment_placeholder_workaround]
          #[derive(Debug, Clone, PartialEq, Eq, Hash)]
          pub enum #name {
            #(#variants(#variants),)*
          }

          #(#traits)*
        },
        quote! {
          #(
            impl From<#variants> for #name {
              fn from(node: #variants) -> #name {
                #name::#variants(node)
              }
            }
          )*
          #ast_node
        },
      )
    })
    .unzip();

  let (any_node_defs, any_node_boilerplate_impls): (Vec<_>, Vec<_>) = grammar
    .nodes
    .iter()
    .flat_map(|node| node.traits.iter().map(move |t| (t, node)))
    .into_group_map()
    .into_iter()
    .sorted_by_key(|(k, _)| *k)
    .map(|(trait_name, nodes)| {
      let name = format_ident!("Any{}", trait_name);
      let trait_name = format_ident!("{}", trait_name);
      let kinds: Vec<_> = nodes
        .iter()
        .map(|name| format_ident!("{}", to_upper_snake_case(&name.name.to_string())))
        .collect();

      (
        quote! {
          #[pretty_doc_comment_placeholder_workaround]
          #[derive(Debug, Clone, PartialEq, Eq, Hash)]
          pub struct #name {
            pub(crate) syntax: SyntaxNode,
          }
          impl ast::#trait_name for #name {}
        },
        quote! {
          impl #name {
            #[inline]
            pub fn new<T: ast::#trait_name>(node: T) -> #name {
              #name {
                syntax: node.syntax().clone()
              }
            }
          }
          impl AstNode for #name {
            fn can_cast(kind: SyntaxKind) -> bool {
              matches!(kind, #(#kinds)|*)
            }
            fn cast(syntax: SyntaxNode) -> Option<Self> {
              Self::can_cast(syntax.kind()).then(|| #name { syntax })
            }
            fn syntax(&self) -> &SyntaxNode {
              &self.syntax
            }
          }
        },
      )
    })
    .unzip();

  let enum_names = grammar.enums.iter().map(|it| &it.name);
  let node_names = grammar.nodes.iter().map(|it| &it.name);

  let display_impls =
    enum_names.chain(node_names.clone()).map(|it| format_ident!("{}", it)).map(|name| {
      quote! {
        impl std::fmt::Display for #name {
          fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            std::fmt::Display::fmt(self.syntax(), f)
          }
        }
      }
    });

  // Note: might need to import `crate::ext::AstTokenChildren` again.
  let ast = quote! {
    #![allow(non_snake_case, non_camel_case_types)]
    use crate::{
      support, ext::{AstChildren, AstNode},
      node::{SyntaxNode, SyntaxToken},
    };
    use rb_parser::{
      SyntaxKind::{self, *},
      T,
    };

    #(#node_defs)*
    #(#enum_defs)*
    #(#any_node_defs)*
    #(#node_boilerplate_impls)*
    #(#enum_boilerplate_impls)*
    #(#any_node_boilerplate_impls)*
    #(#display_impls)*
  };

  let ast = ast.to_string().replace("T ! [", "T![");

  let mut res = String::with_capacity(ast.len() * 2);

  let mut docs =
    grammar.nodes.iter().map(|it| &it.doc).chain(grammar.enums.iter().map(|it| &it.doc));

  for chunk in ast.split("# [pretty_doc_comment_placeholder_workaround] ") {
    res.push_str(chunk);
    if let Some(doc) = docs.next() {
      write_doc_comment(doc, &mut res);
    }
  }

  let res = sourcegen::add_preamble("sourcegen_ast", sourcegen::reformat(res));
  res.replace("#[derive", "\n#[derive")
}

fn write_doc_comment(contents: &[String], dest: &mut String) {
  for line in contents {
    writeln!(dest, "///{}", line).unwrap();
  }
}

fn generate_syntax_kinds(ast: &AstSrc) -> String {
  let mut keywords: Vec<Ident> = vec![];
  let mut keyword_idents: Vec<Ident> = vec![];
  let mut punctuation: Vec<Ident> = vec![];
  let mut punctuation_values: Vec<TokenStream> = vec![];
  for name in ast.grammar_tokens.iter() {
    if name == "semi" {
      punctuation_values.push(quote!(;));
      let ident = Ident::new(&to_upper_snake_case(name), Span::call_site());
      punctuation.push(ident);
    } else if name == "ident" {
      continue;
    } else if name != "_" && name.chars().all(|c| c.is_ascii_lowercase() || c == '_') {
      let ident = Ident::new(name, Span::call_site());
      keyword_idents.push(ident);

      let enum_name = format!("{}_KW", to_upper_snake_case(name));
      let ident = Ident::new(&enum_name, Span::call_site());
      keywords.push(ident);
    } else {
      let token = name;
      let name = token_name(name);

      if token == "'" {
        punctuation_values.push(quote!('\''));
      } else if token == "\"" {
        punctuation_values.push(quote!('"'));
      } else if token == "\\" {
        punctuation_values.push(quote!('\\'));
      } else if "{}[]()".contains(token) {
        let c = token.chars().next().unwrap();
        punctuation_values.push(quote!(#c));
      } else {
        let cs = token.chars().map(|c| Punct::new(c, Spacing::Joint));
        punctuation_values.push(quote!(#(#cs)*));
      }
      let ident = Ident::new(&to_upper_snake_case(name), Span::call_site());
      punctuation.push(ident);
    }
  }

  // TODO: Need to line these up with the actual grammar
  let mut tokens: Vec<Ident> = vec![];
  for tok in &["WHITESPACE", "COMMENT", "IDENT"] {
    let ident = Ident::new(tok, Span::call_site());
    tokens.push(ident);
  }

  let mut nodes: Vec<Ident> = vec![];
  for node in ast.nodes.iter() {
    if TOKEN_SHORTHANDS.contains(&node.name.as_str()) {
      continue;
    }

    nodes.push(Ident::new(&to_upper_snake_case(&node.name), Span::call_site()));
  }

  let ast = quote! {
    #![allow(bad_style, missing_docs, unreachable_pub)]
    /// The kind of syntax node, e.g. `IDENT`, `USE_KW`, or `STRUCT`.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    #[repr(u16)]
    pub enum SyntaxKind {
      // Technical SyntaxKinds: they appear temporally during parsing,
      // but never end up in the final tree
      #[doc(hidden)]
      TOMBSTONE,
      #[doc(hidden)]
      EOF,
      #[comment_separator]
      #(#punctuation,)*
      #[comment_separator]
      #(#tokens,)*
      #[comment_separator]
      #(#keywords,)*
      #[comment_separator]
      #(#nodes,)*

      // Technical kind so that we can cast from u16 safely
      #[doc(hidden)]
      __LAST,
    }
    use self::SyntaxKind::*;

    impl SyntaxKind {
      pub fn is_keyword(self) -> bool {
        matches!(self, #(#keywords)|*)
      }

      pub fn is_punct(self) -> bool {
        matches!(self, #(#punctuation)|*)
      }

      /*
      pub fn from_keyword(ident: &str) -> Option<SyntaxKind> {
        let kw = match ident {
          #(#full_keywords_values => #full_keywords,)*
          _ => return None,
        };
        Some(kw)
      }

      pub fn from_contextual_keyword(ident: &str) -> Option<SyntaxKind> {
        let kw = match ident {
          #(#contextual_keywords_values => #contextual_keywords,)*
          _ => return None,
        };
        Some(kw)
      }

      pub fn from_char(c: char) -> Option<SyntaxKind> {
        let tok = match c {
          #(#single_byte_tokens_values => #single_byte_tokens,)*
          _ => return None,
        };
        Some(tok)
      }
      */
    }

    #[macro_export]
    macro_rules! T {
      #([#punctuation_values] => { $crate::SyntaxKind::#punctuation };)*
      #([#keyword_idents] => { $crate::SyntaxKind::#keywords };)*
      [lifetime_ident] => { $crate::SyntaxKind::LIFETIME_IDENT };
      [ws] => { $crate::SyntaxKind::WHITESPACE };
      [ident] => { $crate::SyntaxKind::IDENT };
      [shebang] => { $crate::SyntaxKind::SHEBANG };
    }
  };

  sourcegen::add_preamble("sourcegen_ast", sourcegen::reformat(ast.to_string()))
    .replace("#[comment_separator]", "// ---")
}

fn to_upper_snake_case(s: &str) -> String {
  let mut buf = String::with_capacity(s.len());
  let mut prev = false;
  for c in s.chars() {
    if c.is_ascii_uppercase() && prev {
      buf.push('_')
    }
    prev = true;

    buf.push(c.to_ascii_uppercase());
  }
  buf
}

fn to_lower_snake_case(s: &str) -> String {
  let mut buf = String::with_capacity(s.len());
  let mut prev = false;
  for c in s.chars() {
    if c.is_ascii_uppercase() && prev {
      buf.push('_')
    }
    prev = true;

    buf.push(c.to_ascii_lowercase());
  }
  buf
}

#[allow(unused)]
fn to_pascal_case(s: &str) -> String {
  let mut buf = String::with_capacity(s.len());
  let mut prev_is_underscore = true;
  for c in s.chars() {
    if c == '_' {
      prev_is_underscore = true;
    } else if prev_is_underscore {
      buf.push(c.to_ascii_uppercase());
      prev_is_underscore = false;
    } else {
      buf.push(c.to_ascii_lowercase());
    }
  }
  buf
}

fn pluralize(s: &str) -> String { format!("{}s", s) }

fn token_name(name: &str) -> &str {
  match name {
    "(" | "'('" => "open_paren",
    ")" | "')'" => "close_paren",
    "[" | "'['" => "open_bracket",
    "]" | "']'" => "close_bracket",
    "{" | "'{'" => "open_curly",
    "}" | "'}'" => "close_curly",

    // punctuation
    "=" => "eq",
    ":" => "colon",
    "->" => "thin_arrow",
    "=>" => "fat_arrow",
    "#" => "pound",
    "," => "comma",

    // operators
    "." => "dot",

    // math
    "-" => "minus",
    "+" => "plus",
    "*" => "star",
    "/" => "slash",
    "&&" => "and",
    "||" => "or",
    "&" => "bit_and",
    "|" => "bit_or",
    "^" => "bit_xor",
    "==" => "eq_eq",
    "!=" => "not_eq",
    ">=" => "greater_eq",
    "<=" => "less_eq",
    "<" => "less",
    ">" => "greater",

    "'" => "single_quote",
    "\"" => "double_quote",
    "\\" => "backslash",

    _ if name.chars().all(|c| c.is_ascii_lowercase() || c == '_') => name,
    _ => panic!("unknown token {name}"),
  }
}

impl Field {
  fn is_many(&self) -> bool { matches!(self, Field::Node { cardinality: Cardinality::Many, .. }) }
  fn token_kind(&self) -> Option<proc_macro2::TokenStream> {
    match self {
      Field::Token(token) => match token.as_str() {
        "'" => Some(quote! { T!['\''] }),
        "\"" => Some(quote! { T!['"'] }),
        "\\" => Some(quote! { T!['\\'] }),
        _ => {
          let token: proc_macro2::TokenStream = token.parse().unwrap();
          Some(quote! { T![#token] })
        }
      },
      Field::Node { ty, .. } if TOKEN_SHORTHANDS.contains(&ty.as_str()) => {
        let token: proc_macro2::TokenStream = ty.parse().unwrap();
        Some(quote! { T![#token] })
      }
      _ => None,
    }
  }
  fn method_name(&self) -> proc_macro2::Ident {
    match self {
      Field::Token(name) => {
        let name = token_name(name);
        format_ident!("{}_token", name)
      }
      Field::Node { name, .. } if TOKEN_SHORTHANDS.contains(&name.as_str()) => {
        format_ident!("{}_token", name)
      }
      Field::Node { name, .. } => {
        if name == "type" {
          format_ident!("ty")
        } else {
          format_ident!("{}", name)
        }
      }
    }
  }
  fn ty(&self) -> proc_macro2::Ident {
    match self {
      Field::Token(_) => format_ident!("SyntaxToken"),
      Field::Node { ty, .. } if TOKEN_SHORTHANDS.contains(&ty.as_str()) => {
        format_ident!("SyntaxToken")
      }
      Field::Node { ty, .. } => format_ident!("{}", ty),
    }
  }
}

// These types are short, and its easier to write "nl" than "'nl'".
const TOKEN_SHORTHANDS: &[&str] = &["nl"];

fn lower(grammar: &Grammar) -> AstSrc {
  // FIXME: Maybe remove tokens?.
  let mut res = AstSrc {
    tokens: "Ident".split_ascii_whitespace().map(|it| it.to_string()).collect::<Vec<_>>(),
    grammar_tokens: grammar.tokens().map(|it| grammar[it].name.clone()).collect::<Vec<_>>(),
    ..Default::default()
  };

  let nodes = grammar.iter().collect::<Vec<_>>();

  for &node in &nodes {
    let name = grammar[node].name.clone();

    if TOKEN_SHORTHANDS.contains(&name.as_str()) {
      continue;
    }

    let rule = &grammar[node].rule;
    match lower_enum(grammar, rule) {
      Some(variants) => {
        let enum_src = AstEnumSrc { doc: Vec::new(), name, traits: Vec::new(), variants };
        res.enums.push(enum_src);
      }
      None => {
        let mut fields = Vec::new();
        lower_rule(&mut fields, grammar, None, rule);
        res.nodes.push(AstNodeSrc { doc: Vec::new(), name, traits: Vec::new(), fields });
      }
    }
  }

  deduplicate_fields(&mut res);
  extract_enums(&mut res);
  extract_struct_traits(&mut res);
  extract_enum_traits(&mut res);
  res
}

fn lower_enum(grammar: &Grammar, rule: &Rule) -> Option<Vec<String>> {
  let alternatives = match rule {
    Rule::Alt(it) => it,
    _ => return None,
  };
  let mut variants = Vec::new();
  for alternative in alternatives {
    match alternative {
      Rule::Node(it) => variants.push(grammar[*it].name.clone()),
      Rule::Token(it) if grammar[*it].name == ";" => (),
      _ => return None,
    }
  }
  Some(variants)
}

fn lower_rule(acc: &mut Vec<Field>, grammar: &Grammar, label: Option<&String>, rule: &Rule) {
  if lower_comma_list(acc, grammar, label, rule) {
    return;
  }

  match rule {
    Rule::Node(node) => {
      let ty = grammar[*node].name.clone();
      let name = label.cloned().unwrap_or_else(|| to_lower_snake_case(&ty));
      let field = Field::Node { name, ty, cardinality: Cardinality::Optional };
      acc.push(field);
    }
    Rule::Token(token) => {
      assert!(label.is_none());
      let mut name = grammar[*token].name.clone();
      if "[]{}()".contains(&name) {
        name = format!("'{}'", name);
      }
      let field = Field::Token(name);
      acc.push(field);
    }
    Rule::Rep(inner) => match **inner {
      Rule::Node(node) => {
        let ty = grammar[node].name.clone();
        let name = label.cloned().unwrap_or_else(|| pluralize(&to_lower_snake_case(&ty)));
        let field = Field::Node { name, ty, cardinality: Cardinality::Many };
        acc.push(field);
      }
      _ => println!("unhandled rep: {:?}", rule),
    },
    Rule::Labeled { label: l, rule } => {
      assert!(label.is_none());
      let manually_implemented = matches!(l.as_str(), "lhs" | "rhs");
      if manually_implemented {
        return;
      }
      lower_rule(acc, grammar, Some(l), rule);
    }
    Rule::Seq(rules) | Rule::Alt(rules) => {
      for rule in rules {
        lower_rule(acc, grammar, label, rule)
      }
    }
    Rule::Opt(rule) => lower_rule(acc, grammar, label, rule),
  }
}

// (T (',' T)*)
fn lower_comma_list(
  acc: &mut Vec<Field>,
  grammar: &Grammar,
  label: Option<&String>,
  rule: &Rule,
) -> bool {
  let rule = match rule {
    Rule::Seq(it) => it,
    _ => return false,
  };
  let node = match rule.as_slice() {
    [Rule::Node(node), Rule::Rep(_)] => node,
    _ => return false,
  };
  let ty = grammar[*node].name.clone();
  let name = label.cloned().unwrap_or_else(|| pluralize(&to_lower_snake_case(&ty)));
  let field = Field::Node { name, ty, cardinality: Cardinality::Many };
  acc.push(field);
  true
}

fn deduplicate_fields(ast: &mut AstSrc) {
  for node in &mut ast.nodes {
    let mut i = 0;
    'outer: while i < node.fields.len() {
      for j in 0..i {
        let f1 = &node.fields[i];
        let f2 = &node.fields[j];
        if f1 == f2 {
          node.fields.remove(i);
          continue 'outer;
        }
      }
      i += 1;
    }
  }
}

fn extract_enums(ast: &mut AstSrc) {
  for node in &mut ast.nodes {
    for enm in &ast.enums {
      let mut to_remove = Vec::new();
      for (i, field) in node.fields.iter().enumerate() {
        let ty = field.ty().to_string();
        if enm.variants.iter().any(|it| it == &ty) {
          to_remove.push(i);
        }
      }
      if to_remove.len() == enm.variants.len() {
        node.remove_field(to_remove);
        let ty = enm.name.clone();
        let name = to_lower_snake_case(&ty);
        node.fields.push(Field::Node { name, ty, cardinality: Cardinality::Optional });
      }
    }
  }
}

fn extract_struct_traits(_ast: &mut AstSrc) {
  /*
  let traits: &[(&str, &[&str])] = &[
    ("HasAttrs", &["attrs"]),
    ("HasName", &["name"]),
    ("HasVisibility", &["visibility"]),
    ("HasGenericParams", &["generic_param_list", "where_clause"]),
    ("HasTypeBounds", &["type_bound_list", "colon_token"]),
    ("HasModuleItem", &["items"]),
    ("HasLoopBody", &["label", "loop_body"]),
    ("HasArgList", &["arg_list"]),
  ];

  for node in &mut ast.nodes {
    for (name, methods) in traits {
      extract_struct_trait(node, name, methods);
    }
  }
  */

  // TODO: Do I need this?
  /*
  let nodes_with_doc_comments = [
    "SourceFile",
    "Fn",
    "Struct",
    "Union",
    "RecordField",
    "TupleField",
    "Enum",
    "Variant",
    "Trait",
    "Module",
    "Static",
    "Const",
    "TypeAlias",
    "Impl",
    "ExternBlock",
    "ExternCrate",
    "MacroCall",
    "MacroRules",
    "MacroDef",
    "Use",
  ];

  for node in &mut ast.nodes {
    if nodes_with_doc_comments.contains(&&*node.name) {
      node.traits.push("HasDocComments".into());
    }
  }
  */
}

fn extract_enum_traits(ast: &mut AstSrc) {
  for enm in &mut ast.enums {
    if enm.name == "Stmt" {
      continue;
    }
    let nodes = &ast.nodes;
    let mut variant_traits = enm
      .variants
      .iter()
      .filter_map(|var| nodes.iter().find(|it| &it.name == var))
      .map(|node| node.traits.iter().cloned().collect::<BTreeSet<_>>());

    let mut enum_traits = match variant_traits.next() {
      Some(it) => it,
      None => continue,
    };
    for traits in variant_traits {
      enum_traits = enum_traits.intersection(&traits).cloned().collect();
    }
    enm.traits = enum_traits.into_iter().collect();
  }
}

impl AstNodeSrc {
  fn remove_field(&mut self, to_remove: Vec<usize>) {
    to_remove.into_iter().rev().for_each(|idx| {
      self.fields.remove(idx);
    });
  }
}
