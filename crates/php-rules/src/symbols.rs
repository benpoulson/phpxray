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

/// PHP's superglobals — the variables visible in every scope without `global`.
///
/// Names are given without the leading `$`.
pub(crate) const SUPERGLOBALS: &[&str] = &[
    "GLOBALS", "_SERVER", "_GET", "_POST", "_FILES", "_COOKIE", "_SESSION", "_REQUEST", "_ENV",
];

/// Variables a definedness check must never report as possibly-undefined.
///
/// A **superset** of [`SUPERGLOBALS`], and deliberately a different question:
/// `$this`, `$argc`/`$argv` and `$http_response_header` are not superglobals, but
/// they are populated by the engine rather than by any statement the analyzer can
/// see. Keeping the superglobal part shared means the two lists cannot disagree
/// about the actual superglobals.
pub(crate) fn is_always_defined(name: &str) -> bool {
    const ENGINE_POPULATED: &[&str] = &[
        "this",
        "http_response_header",
        "argc",
        "argv",
        "php_errormsg",
    ];
    SUPERGLOBALS.contains(&name) || ENGINE_POPULATED.contains(&name)
}

pub(crate) fn fqn_key(fqn: &str) -> String {
    SymbolKey::class_like(fqn).into_string()
}

pub(crate) fn same_fqn(a: &str, b: &str) -> bool {
    SymbolKey::same(SymbolKind::ClassLike, a, b)
}

pub(crate) fn class_tree_fully_known(fa: &FileAnalysis, fqn: &str) -> bool {
    fa.class_fully_known(fqn)
}
