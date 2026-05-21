//! Shared symbol identity helpers for rules.

use crate::FileAnalysis;
use php_resolve::{SymbolKey, SymbolKind};

pub(crate) fn fqn_key(fqn: &str) -> String {
    SymbolKey::class_like(fqn).into_string()
}

pub(crate) fn same_fqn(a: &str, b: &str) -> bool {
    SymbolKey::same(SymbolKind::ClassLike, a, b)
}

pub(crate) fn class_tree_fully_known(fa: &FileAnalysis, fqn: &str) -> bool {
    fa.class_fully_known(fqn)
}
