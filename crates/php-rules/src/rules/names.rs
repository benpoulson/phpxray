//! phpstan category **Names** — rule replication.
//!
//! Source: `phpstan-src/src/Rules/Names/` — 1 rule at level 0.
//! Checklist: docs/phpstan-rules.md. Add each rule as a `RuleEntry` to
//! `RULES` (with a phpstan-style identifier on its diagnostics).
//!
//! Implemented here:
//! - **UsedNamesRule** (`class.nameInUse`/`interface.nameInUse`/`trait.nameInUse`/
//!   `enum.nameInUse`/`use.nameInUse`, level 0) — within one file, a class-like
//!   declaration or a `use` alias whose (case-insensitive) name was already
//!   declared/imported earlier *in the same namespace*. Class-like names and `use`
//!   aliases share one per-namespace pool (matching phpstan), so `use X\Foo;` then
//!   `class Foo {}` collide. Only class imports participate (`use function`/`use
//!   const` are ignored). Purely structural — only *direct* namespace children are
//!   considered (a conditional `if (…) { class A {} }` is not), exactly like phpstan.

use crate::{FileAnalysis, RuleEntry};
use php_ast::{ClassDecl, ClassKind, StmtKind, UseItem, UseKind};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_resolve::for_each_region;
use std::collections::HashMap;

fn run_used_names(fa: &FileAnalysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Per-namespace (lowercased) pool of already-declared class-like names and
    // `use` aliases. Shared across regions so repeated `namespace X;` blocks
    // accumulate, exactly as phpstan keys by namespace name.
    let mut used: HashMap<String, Vec<String>> = HashMap::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        let ns = scope.namespace().unwrap_or("");
        let bucket = used.entry(ns.to_ascii_lowercase()).or_default();
        for st in region {
            match &st.kind {
                StmtKind::Use(items) => {
                    check_uses(items, "", false, fa.interner, bucket, &mut out);
                }
                StmtKind::GroupUse { prefix, kind, items } => {
                    let ignore_all = matches!(kind, Some(UseKind::Function | UseKind::Const));
                    check_uses(items, &prefix.text, ignore_all, fa.interner, bucket, &mut out);
                }
                StmtKind::Class(decl) => {
                    check_class(decl, st.span, ns, fa.interner, bucket, &mut out);
                }
                _ => {}
            }
        }
    });
    out
}

/// The lowercase type word + nonIgnorable identifier for a class-like kind.
fn kind_words(kind: ClassKind) -> (&'static str, &'static str) {
    match kind {
        ClassKind::Class => ("class", "class.nameInUse"),
        ClassKind::Interface => ("interface", "interface.nameInUse"),
        ClassKind::Trait => ("trait", "trait.nameInUse"),
        ClassKind::Enum => ("enum", "enum.nameInUse"),
    }
}

fn check_class(
    decl: &ClassDecl,
    span: php_span::Span,
    ns: &str,
    interner: &Interner,
    bucket: &mut Vec<String>,
    out: &mut Vec<Diagnostic>,
) {
    let Some(name_sym) = decl.name else { return }; // anonymous class — no name
    let name = interner.resolve(name_sym);
    let name_lc = name.to_ascii_lowercase();
    let (word, code) = kind_words(decl.kind);
    if bucket.contains(&name_lc) {
        let qualified = if ns.is_empty() { name.to_string() } else { format!("{ns}\\{name}") };
        out.push(
            Diagnostic::error(
                span,
                format!("Cannot declare {word} {qualified} because the name is already in use."),
            )
            .with_code(code),
        );
    } else {
        bucket.push(name_lc);
    }
}

fn check_uses(
    items: &[UseItem],
    group_prefix: &str,
    ignore_all: bool,
    interner: &Interner,
    bucket: &mut Vec<String>,
    out: &mut Vec<Diagnostic>,
) {
    for item in items {
        // Only class imports collide in the class name pool.
        if ignore_all || item.kind != UseKind::Class {
            continue;
        }
        let alias = match item.alias {
            Some(a) => interner.resolve(a).to_string(),
            None => last_segment(&item.name.text),
        };
        let alias_lc = alias.to_ascii_lowercase();
        if bucket.contains(&alias_lc) {
            let full = if group_prefix.is_empty() {
                item.name.text.clone()
            } else {
                format!("{group_prefix}\\{}", item.name.text)
            };
            out.push(
                Diagnostic::error(
                    item.name.span,
                    format!("Cannot use {full} as {alias} because the name is already in use."),
                )
                .with_code("use.nameInUse"),
            );
        } else {
            bucket.push(alias_lc);
        }
    }
}

/// The last `\`-separated segment of a name (its default import alias).
fn last_segment(text: &str) -> String {
    text.trim_start_matches('\\').rsplit('\\').next().unwrap_or(text).to_string()
}

pub(crate) static RULES: &[RuleEntry] =
    &[RuleEntry { name: "use.nameInUse", level: 0, run: run_used_names }];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    #[test]
    fn duplicate_class_name_in_file() {
        let src = r#"<?php class A {} class A {}"#;
        assert_eq!(codes(src, run_used_names), ["class.nameInUse"]);
    }

    #[test]
    fn duplicate_interface_and_trait() {
        assert_eq!(codes(r#"<?php interface I {} interface I {}"#, run_used_names), ["interface.nameInUse"]);
        assert_eq!(codes(r#"<?php trait T {} trait T {}"#, run_used_names), ["trait.nameInUse"]);
        assert_eq!(codes(r#"<?php enum E {} enum E {}"#, run_used_names), ["enum.nameInUse"]);
    }

    #[test]
    fn distinct_names_are_ok() {
        assert!(codes(r#"<?php class A {} class B {}"#, run_used_names).is_empty());
    }

    #[test]
    fn case_insensitive() {
        assert_eq!(codes(r#"<?php class Foo {} class foo {}"#, run_used_names), ["class.nameInUse"]);
    }

    #[test]
    fn different_namespaces_do_not_collide() {
        let src = r#"<?php
            namespace A { class Foo {} }
            namespace B { class Foo {} }"#;
        assert!(codes(src, run_used_names).is_empty());
    }

    #[test]
    fn same_namespace_blocks_accumulate() {
        let src = r#"<?php
            namespace A { class Foo {} }
            namespace A { class Foo {} }"#;
        assert_eq!(codes(src, run_used_names), ["class.nameInUse"]);
    }

    #[test]
    fn duplicate_use_alias() {
        let src = r#"<?php
            use Foo\Bar;
            use Baz\Bar;"#;
        assert_eq!(codes(src, run_used_names), ["use.nameInUse"]);
    }

    #[test]
    fn use_then_class_same_name_collide() {
        let src = r#"<?php
            use Foo\Bar;
            class Bar {}"#;
        assert_eq!(codes(src, run_used_names), ["class.nameInUse"]);
    }

    #[test]
    fn aliased_use_does_not_collide() {
        let src = r#"<?php
            use Foo\Bar;
            use Baz\Bar as Qux;"#;
        assert!(codes(src, run_used_names).is_empty());
    }

    #[test]
    fn function_and_const_use_are_ignored() {
        let src = r#"<?php
            use function Foo\bar;
            use const Foo\bar;
            use Foo\bar;"#;
        // The class import `use Foo\bar;` is the first in the class pool — no collision.
        assert!(codes(src, run_used_names).is_empty());
    }

    #[test]
    fn conditional_declaration_not_checked() {
        // A class nested in an `if` is not a direct namespace child.
        let src = r#"<?php class A {} if (true) { class A {} }"#;
        assert!(codes(src, run_used_names).is_empty());
    }
}
