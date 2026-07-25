//! Laravel facade-alias resolution (opt-in via the `laravelAliases` config).
//!
//! Laravel registers a set of global class aliases at runtime (`Sentry`, `Str`,
//! …) so facades can be referenced by short name. Static analysis never runs the
//! framework, so those names look undefined and produce `class.notFound`. We
//! reconstruct the same alias map from the two places Laravel reads it:
//!
//!   * **package auto-discovery** — every installed package's
//!     `extra.laravel.aliases`, aggregated in `vendor/composer/installed.json`;
//!   * **the application** — `config/app.php`'s `aliases` array.
//!
//! Best-effort: missing/unreadable/unexpected inputs are skipped silently.

use php_ast::{Expr, ExprKind, MemberName, StmtKind};
use php_intern::Interner;
use php_resolve::{for_each_region, Resolution, Scope};
use std::collections::BTreeMap;
use std::path::Path;

/// Collect the runtime class aliases (`alias name` → `target FQN`) for a project
/// root. Deterministic order; first definition of a name wins.
pub fn collect_facade_aliases(root: &Path) -> Vec<(String, String)> {
    let mut out: BTreeMap<String, String> = BTreeMap::new();
    aliases_from_installed_json(root, &mut out);
    aliases_from_config_app(root, &mut out);
    out.into_iter().collect()
}

/// Package auto-discovery: `vendor/composer/installed.json` lists every package
/// with its `extra.laravel.aliases` map. Composer 2 wraps the list in a
/// `{ "packages": [...] }` object; composer 1 is a bare array.
fn aliases_from_installed_json(root: &Path, out: &mut BTreeMap<String, String>) {
    let Ok(text) = std::fs::read_to_string(root.join("vendor/composer/installed.json")) else {
        return;
    };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else {
        return;
    };
    let packages = json
        .get("packages")
        .and_then(|p| p.as_array())
        .or_else(|| json.as_array());
    let Some(packages) = packages else { return };
    for pkg in packages {
        let Some(aliases) = pkg
            .pointer("/extra/laravel/aliases")
            .and_then(|a| a.as_object())
        else {
            continue;
        };
        for (alias, target) in aliases {
            if let Some(t) = target.as_str() {
                out.entry(alias.clone())
                    .or_insert_with(|| t.trim_start_matches('\\').to_string());
            }
        }
    }
}

/// The application's `config/app.php` `aliases` array. Parsed with our own front
/// end so `Facade::class` values resolve through the file's `use` imports.
fn aliases_from_config_app(root: &Path, out: &mut BTreeMap<String, String>) {
    let Ok(text) = std::fs::read_to_string(root.join("config/app.php")) else {
        return;
    };
    let parsed = php_parser::parse(&text);
    for_each_region(&parsed.program.stmts, &parsed.interner, |scope, region| {
        for stmt in region {
            if let StmtKind::Return(Some(expr)) = &stmt.kind {
                collect_config_aliases(expr, scope, &parsed.interner, out);
            }
        }
    });
}

/// Find `'aliases' => [ 'Name' => Class::class, … ]` in the returned config array
/// and record each entry.
fn collect_config_aliases(
    expr: &Expr,
    scope: &Scope,
    interner: &Interner,
    out: &mut BTreeMap<String, String>,
) {
    let ExprKind::Array { items, .. } = &expr.kind else {
        return;
    };
    for item in items {
        let (Some(key), Some(value)) = (&item.key, &item.value) else {
            continue;
        };
        if str_literal(key).as_deref() != Some("aliases") {
            continue;
        }
        let ExprKind::Array { items: aliases, .. } = &value.kind else {
            continue;
        };
        for a in aliases {
            let (Some(k), Some(v)) = (&a.key, &a.value) else {
                continue;
            };
            if let (Some(alias), Some(target)) = (str_literal(k), class_ref_fqn(v, scope, interner))
            {
                out.entry(alias).or_insert(target);
            }
        }
    }
}

/// The UTF-8 value of a string-literal expression.
fn str_literal(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Str(bytes) => std::str::from_utf8(bytes).ok().map(str::to_string),
        _ => None,
    }
}

/// Resolve an alias target: `Class::class` (through the file's imports) or a
/// literal fully-qualified class-name string.
fn class_ref_fqn(e: &Expr, scope: &Scope, interner: &Interner) -> Option<String> {
    match &e.kind {
        ExprKind::ClassConst {
            class,
            name: MemberName::Ident(sym),
        } if interner.resolve(*sym).eq_ignore_ascii_case("class") => {
            let ExprKind::Name(n) = &class.kind else {
                return None;
            };
            match scope.resolve_class(n) {
                Resolution::Fqn(f) | Resolution::Fallback { namespaced: f, .. } => {
                    Some(f.trim_start_matches('\\').to_string())
                }
                _ => None,
            }
        }
        ExprKind::Str(bytes) => std::str::from_utf8(bytes)
            .ok()
            .map(|s| s.trim_start_matches('\\').to_string()),
        _ => None,
    }
}
