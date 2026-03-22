//! Analysis rules — the start of the diagnostics engine that runs on top of the
//! resolved AST and the project symbol index.
//!
//! The first rule is **unknown-symbol detection**: a reference whose resolved
//! name is not declared anywhere in the project and is not a PHP built-in is an
//! error. This is the payoff of the index + built-in stubs: classes/functions/
//! constants that don't exist get flagged.

use php_diagnostics::Diagnostic;
use php_index::ProjectIndex;
use php_resolve::{RefKind, Resolution, ResolvedRef};

mod registry;
mod return_type;
mod rules;
mod walk;
#[cfg(test)]
mod testutil;
pub use registry::{analyze_file, rules_for_level, FileAnalysis, RuleEntry};
pub use return_type::return_type_errors;

/// Report every reference in `refs` whose target is unknown to `index` (neither
/// a project declaration nor a PHP built-in). `index` must already contain the
/// whole project's declarations plus the built-ins (see
/// [`ProjectIndex::with_builtins`]).
///
/// Function/constant references honour PHP's global fallback: an unqualified
/// name in a namespace is "known" if *either* the namespaced or the global
/// symbol exists.
pub fn unknown_symbols(index: &ProjectIndex, refs: &[ResolvedRef]) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for r in refs {
        let unknown = match (r.kind, &r.resolution) {
            // `self`/`parent`/`static` are resolved against the class context,
            // not the index.
            (_, Resolution::LateStatic(_)) => continue,
            // Built-in scalar types never reach here (filtered during resolution).
            (_, Resolution::BuiltinType(_)) => continue,

            (RefKind::Class, Resolution::Fqn(fqn)) => {
                (!index.has_class(fqn)).then(|| ("class", fqn.clone()))
            }
            (RefKind::Function, res) => {
                callable_missing(res, |n| index.has_function(n)).then(|| ("function", primary(res)))
            }
            (RefKind::Const, res) => {
                callable_missing(res, |n| index.has_constant(n)).then(|| ("constant", primary(res)))
            }
            // A class reference that isn't a plain name (shouldn't occur).
            (RefKind::Class, _) => None,
        };
        if let Some((what, name)) = unknown {
            let code = match what {
                "class" => "class.notFound",
                "function" => "function.notFound",
                _ => "constant.notFound",
            };
            out.push(Diagnostic::error(r.span, format!("unknown {what} `{name}`")).with_code(code));
        }
    }
    out
}

/// Whether a function/constant resolution refers to nothing the index knows,
/// honouring the global fallback (a fallback is missing only if *both*
/// candidates are absent).
fn callable_missing(res: &Resolution, exists: impl Fn(&str) -> bool) -> bool {
    match res {
        Resolution::Fqn(fqn) => !exists(fqn),
        // Global fallback: known if either candidate exists.
        Resolution::Fallback { namespaced, global } => !exists(namespaced) && !exists(global),
        // LateStatic/BuiltinType handled by the caller.
        _ => false,
    }
}

/// The name to show for a resolution (the namespaced candidate for a fallback).
fn primary(res: &Resolution) -> String {
    match res {
        Resolution::Fqn(s) | Resolution::Fallback { namespaced: s, .. } => s.clone(),
        Resolution::LateStatic(s) | Resolution::BuiltinType(s) => s.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_resolve::{index_file, resolve_references};

    /// Analyse one file as a whole project (its own declarations + built-ins).
    fn unknowns(src: &str) -> Vec<String> {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors in test source");
        let mut index = ProjectIndex::with_builtins();
        index.add_file("test.php", &index_file(&r.program, &r.interner));
        let refs = resolve_references(&r.program, &r.interner);
        unknown_symbols(&index, &refs).into_iter().map(|d| d.message).collect()
    }

    #[test]
    fn builtins_are_known() {
        let d = unknowns(r#"<?php strlen("x"); new Exception(); echo PHP_EOL; $a instanceof Countable;"#);
        assert!(d.is_empty(), "builtins should be known: {d:?}");
    }

    #[test]
    fn non_core_extension_symbols_are_known() {
        // phpstorm-stubs covers PECL/optional extensions a local PHP build often
        // lacks (sqlsrv/mssql, oci8, redis, …) — these must not be flagged.
        let d = unknowns(
            r#"<?php
            sqlsrv_connect("s", []);
            oci_connect("u", "p", "db");
            $r = new Redis();
            $i = new Imagick();
            "#,
        );
        assert!(d.is_empty(), "non-core extension symbols should be known: {d:?}");
    }

    #[test]
    fn builtin_call_inside_namespace_uses_global_fallback() {
        let d = unknowns(r#"<?php namespace App; strlen("x"); echo PHP_EOL;"#);
        assert!(d.is_empty(), "global fallback should find builtins: {d:?}");
    }

    #[test]
    fn unknown_class_is_reported() {
        let d = unknowns(r#"<?php namespace App; new TotallyMadeUp();"#);
        assert_eq!(d, ["unknown class `App\\TotallyMadeUp`"]);
    }

    #[test]
    fn unknown_function_and_constant() {
        let d = unknowns(r#"<?php no_such_function(); echo NO_SUCH_CONST;"#);
        assert!(d.contains(&"unknown function `no_such_function`".to_string()));
        assert!(d.contains(&"unknown constant `NO_SUCH_CONST`".to_string()));
    }

    #[test]
    fn project_declarations_are_known() {
        let d = unknowns(
            r#"<?php
            namespace App;
            class Base {}
            class User extends Base {}
            function helper() {}
            const LIMIT = 1;
            new User(); helper(); echo LIMIT;
            "#,
        );
        assert!(d.is_empty(), "project symbols should be known: {d:?}");
    }

    #[test]
    fn imported_but_undefined_class_is_unknown() {
        // The import resolves the name, but nothing declares the target.
        let d = unknowns(r#"<?php namespace App; use Vendor\Gone; new Gone();"#);
        assert_eq!(d, ["unknown class `Vendor\\Gone`"]);
    }

    #[test]
    fn self_and_parent_are_not_flagged() {
        let d = unknowns(
            r#"<?php class B {} class C extends B { function m() { new self(); new parent(); new static(); } }"#,
        );
        assert!(d.is_empty(), "late-static refs are not index lookups: {d:?}");
    }

    #[test]
    fn user_function_shadowing_in_namespace_is_known() {
        // `App\helper()` is defined; the unqualified call resolves to it (fallback
        // to global not needed).
        let d = unknowns(r#"<?php namespace App; function helper() {} helper();"#);
        assert!(d.is_empty(), "{d:?}");
    }
}
