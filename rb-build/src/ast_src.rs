//! Defines input for code generation process.

pub(crate) struct KindsSrc<'a> {
  pub(crate) literals: &'a [&'a str],
}

pub(crate) const KINDS_SRC: KindsSrc<'_> = KindsSrc {
  literals: &["INT_NUMBER", "FLOAT_NUMBER", "CHAR", "BYTE", "STRING", "BYTE_STRING", "C_STRING"],
};

#[derive(Default, Debug)]
pub(crate) struct AstSrc {
  pub(crate) tokens:         Vec<String>,
  pub(crate) grammar_tokens: Vec<String>,
  pub(crate) nodes:          Vec<AstNodeSrc>,
  pub(crate) enums:          Vec<AstEnumSrc>,
}

#[derive(Debug)]
pub(crate) struct AstNodeSrc {
  pub(crate) doc:    Vec<String>,
  pub(crate) name:   String,
  pub(crate) traits: Vec<String>,
  pub(crate) fields: Vec<Field>,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Field {
  Token(String),
  Node { name: String, ty: String, cardinality: Cardinality },
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Cardinality {
  Optional,
  Many,
}

#[derive(Debug)]
pub(crate) struct AstEnumSrc {
  pub(crate) doc:      Vec<String>,
  pub(crate) name:     String,
  pub(crate) traits:   Vec<String>,
  pub(crate) variants: Vec<String>,
}
