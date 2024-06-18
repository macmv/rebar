//! The actual rebar parser.

use crate::{syntax_kind::SyntaxKind::*, Parser};

mod expr;
mod stmt;

pub mod entry_point;
