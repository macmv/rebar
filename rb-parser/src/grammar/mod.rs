//! The actual rebar parser.

use crate::{syntax_kind::SyntaxKind::*, Parser};

mod expr;
mod stmt;
mod types;

pub mod entry_point;
