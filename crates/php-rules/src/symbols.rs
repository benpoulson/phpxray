//! Shared symbol identity helpers for rules.

use crate::FileAnalysis;
use php_resolve::{SymbolKey, SymbolKind};

/// The FQN an anonymous class is keyed by, matching the placeholder PHP itself
/// prints in messages.
///
/// It deliberately resolves to nothing in the reflection index: the rules that
/// gate on a class being indexed (member existence, hierarchy checks) then skip
/// anonymous classes rather than judging them against a definition that was
/// never registered. Note two anonymous classes in one file share this name, so
/// it identifies the *kind*, never the instance — never use it as a map key.
pub(crate) const ANONYMOUS_CLASS: &str = "class@anonymous";

/// PHP's superglobals and the always-defined set both live in `php-infer` (the
/// crate that computes definedness); re-exported here so rule code keeps one
/// import path. They were hand-copied twins across the two crates until now.
pub(crate) use php_infer::{is_always_defined, SUPERGLOBALS};

pub(crate) fn fqn_key(fqn: &str) -> String {
    SymbolKey::class_like(fqn).into_string()
}

pub(crate) fn same_fqn(a: &str, b: &str) -> bool {
    SymbolKey::same(SymbolKind::ClassLike, a, b)
}

pub(crate) fn class_tree_fully_known(fa: &FileAnalysis, fqn: &str) -> bool {
    fa.class_fully_known(fqn)
}
