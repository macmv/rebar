//! The actual rebar parser.

use crate::{Parser, syntax_kind::SyntaxKind::*};

mod expr;
mod stmt;
mod types;

pub mod entry_point;
