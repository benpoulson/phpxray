//! phpstan category **Namespaces** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Namespaces/` — 2 rules at level 0.
//! Checklist: docs/phpstan-rules.md.
//!
//! Replicates `ExistingNamesInUseRule` and `ExistingNamesInGroupUseRule`.
//!
//! Fidelity note — what phpstan actually flags here. Both rules dispatch by the
//! *kind* of import:
//!   * `use const C;`     → reports `constant.notFound` ("Used constant %s not found.")
//!   * `use function f;`  → reports `function.notFound` ("Used function %s not found.")
//!   * `use Foo\Bar;`     → delegates to `ClassNameCheck::checkClassNames(..., null)`.
//!
//! With `$location === null` (which is what the use rules pass), `ClassNameCheck`
//! runs **only** the case-sensitivity and forbidden-name checks — it does **not**
//! check class *existence*. So phpstan deliberately does NOT emit `class.notFound`
//! for a `use` of a missing class (that error surfaces at the real usage site, via
//! `new` / `instanceof` / a type hint). We mirror that: class imports emit nothing
//! here. The `*.nameCase` variants need case-preserving builtin reflection that our
//! names-only index can't provide without false positives — DEFERRED.
//!
//! `use` names a fully-qualified symbol regardless of the current namespace, so the
//! import name *is* the FQN — there's no global fallback to honour (unlike a bare
//! function/const *call*). We look the FQN up directly in `fa.project`, which
//! carries builtin function/constant names alongside project declarations, so a
//! `use function strlen;` / `use const PHP_EOL;` of a builtin is never flagged.

#![allow(unused_imports)]
use crate::{walk, FileAnalysis, RuleEntry};
use php_ast::{Name, StmtKind, UseItem, UseKind};
use php_diagnostics::Diagnostic;

/// `\Foo\Bar` and `Foo\Bar` denote the same FQN in a `use`; strip the leading
/// separator before looking the name up (the index normalizes too, but be explicit).
fn normalize(text: &str) -> &str {
    text.trim_start_matches('\\')
}

/// Emit the not-found diagnostic for one (already fully-qualified) import name of a
/// given kind, or `None` if the symbol exists. Class imports never produce an error
/// here (see the module note).
fn check_item(fa: &FileAnalysis, kind: UseKind, name: &Name) -> Option<Diagnostic> {
    let fqn = normalize(&name.text);
    if fqn.is_empty() {
        return None;
    }
    match kind {
        UseKind::Const => (!fa.project.has_constant(fqn)).then(|| {
            Diagnostic::error(name.span, format!("Used constant {fqn} not found."))
                .with_code("constant.notFound")
        }),
        UseKind::Function => (!fa.project.has_function(fqn)).then(|| {
            Diagnostic::error(name.span, format!("Used function {fqn} not found."))
                .with_code("function.notFound")
        }),
        // Class imports: phpstan only checks case-sensitivity (location === null),
        // not existence. Nothing to report.
        UseKind::Class => None,
    }
}

/// phpstan `ExistingNamesInUseRule` (level 0) — `use`, `use function`, `use const`.
fn existing_names_in_use(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::Use(items) = &s.kind {
            for item in items {
                if let Some(d) = check_item(fa, item.kind, &item.name) {
                    out.push(d);
                }
            }
        }
    });
    out
}

/// phpstan `ExistingNamesInGroupUseRule` (level 0) — `use Foo\{Bar, function f, const C};`.
///
/// The effective name of each element is `prefix\element`. Each element's `kind`
/// already reflects the group-level keyword fallback (resolved by the parser), so
/// per-element `function`/`const` overrides are honoured.
fn existing_names_in_group_use(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    walk::for_each_stmt(fa.program, &mut |s| {
        if let StmtKind::GroupUse { prefix, items, .. } = &s.kind {
            let prefix_text = normalize(&prefix.text);
            for item in items {
                let element = normalize(&item.name.text);
                let combined = if prefix_text.is_empty() {
                    element.to_string()
                } else {
                    format!("{prefix_text}\\{element}")
                };
                // Reuse the per-kind check but on the combined FQN, keeping the
                // element's own span for the diagnostic location.
                let full = Name { span: item.name.span, fq: item.name.fq, text: combined };
                if let Some(d) = check_item(fa, item.kind, &full) {
                    out.push(d);
                }
            }
        }
    });
    out
}

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "namespaces/existing-names-in-use",
        level: 0,
        run: existing_names_in_use,
    },
    RuleEntry {
        name: "namespaces/existing-names-in-group-use",
        level: 0,
        run: existing_names_in_group_use,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    // --- ExistingNamesInUseRule -------------------------------------------

    #[test]
    fn use_const_unknown_flagged() {
        let c = codes(
            "<?php use const Foo\\MISSING_CONST;",
            existing_names_in_use,
        );
        assert_eq!(c, vec!["constant.notFound"]);
    }

    #[test]
    fn use_function_unknown_flagged() {
        let c = codes(
            "<?php use function Foo\\missing_function;",
            existing_names_in_use,
        );
        assert_eq!(c, vec!["function.notFound"]);
    }

    #[test]
    fn use_class_unknown_not_flagged() {
        // phpstan does NOT flag a `use` of a missing class (location === null).
        let c = codes("<?php use Foo\\MissingClass;", existing_names_in_use);
        assert!(c.is_empty(), "class imports must not flag existence: {c:?}");
    }

    #[test]
    fn use_function_builtin_ok() {
        let c = codes("<?php use function strlen;", existing_names_in_use);
        assert!(c.is_empty(), "builtin function import must not flag: {c:?}");
    }

    #[test]
    fn use_const_builtin_ok() {
        let c = codes("<?php use const PHP_EOL;", existing_names_in_use);
        assert!(c.is_empty(), "builtin const import must not flag: {c:?}");
    }

    #[test]
    fn use_class_builtin_ok() {
        // ArrayObject is a names-only builtin in the project index — and class
        // imports never flag anyway.
        let c = codes("<?php use ArrayObject;", existing_names_in_use);
        assert!(c.is_empty());
    }

    #[test]
    fn use_function_declared_in_file_ok() {
        let c = codes(
            "<?php namespace App; function helper() {} use function App\\helper;",
            existing_names_in_use,
        );
        assert!(c.is_empty(), "declared function import must not flag: {c:?}");
    }

    #[test]
    fn leading_backslash_normalized() {
        // `use const \PHP_EOL;` is the same symbol; must not flag.
        let c = codes("<?php use const \\PHP_EOL;", existing_names_in_use);
        assert!(c.is_empty(), "leading-backslash builtin const must not flag: {c:?}");
    }

    #[test]
    fn multiple_imports_each_checked() {
        let c = codes(
            "<?php use function strlen, Foo\\nope;",
            existing_names_in_use,
        );
        assert_eq!(c, vec!["function.notFound"]);
    }

    // --- ExistingNamesInGroupUseRule --------------------------------------

    #[test]
    fn group_use_const_unknown_flagged() {
        let c = codes(
            "<?php use const Foo\\{MISSING_A, MISSING_B};",
            existing_names_in_group_use,
        );
        assert_eq!(c, vec!["constant.notFound", "constant.notFound"]);
    }

    #[test]
    fn group_use_function_unknown_flagged() {
        let c = codes(
            "<?php use function Foo\\{missing_one};",
            existing_names_in_group_use,
        );
        assert_eq!(c, vec!["function.notFound"]);
    }

    #[test]
    fn group_use_class_not_flagged() {
        let c = codes(
            "<?php use Foo\\{Bar, Baz};",
            existing_names_in_group_use,
        );
        assert!(c.is_empty(), "group class imports must not flag existence: {c:?}");
    }

    #[test]
    fn group_use_mixed_kinds() {
        // Per-element `function`/`const` keywords inside a plain group use.
        let c = codes(
            "<?php use Foo\\{function missing_fn, const MISSING_C, SomeClass};",
            existing_names_in_group_use,
        );
        assert_eq!(c, vec!["function.notFound", "constant.notFound"]);
    }

    #[test]
    fn group_use_prefix_applied_to_each_element() {
        // Each element's FQN is `prefix\element`; both resolve to unknown here.
        let c = codes(
            "<?php use function Foo\\{a, b};",
            existing_names_in_group_use,
        );
        assert_eq!(c, vec!["function.notFound", "function.notFound"]);
    }

    #[test]
    fn group_use_const_declared_in_file_ok() {
        let c = codes(
            "<?php namespace App; const FOO = 1; use const App\\{FOO};",
            existing_names_in_group_use,
        );
        assert!(c.is_empty(), "declared const group import must not flag: {c:?}");
    }
}
