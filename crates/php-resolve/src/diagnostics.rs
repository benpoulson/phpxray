//! M-R3: single-file diagnostics that fall out of name resolution — **unused
//! imports** and **duplicate imports**. (Cross-file checks like "unknown class"
//! belong to a later rules engine once a multi-file symbol index exists.)

use crate::index::for_each_region;
use crate::references::{collect_region, RefKind};
use php_ast::{NameFq, Stmt, StmtKind, UseItem, UseKind};
use php_diagnostics::Diagnostic;
use php_intern::Interner;
use php_span::Span;

/// Resolution diagnostics for one parsed file, in source order.
pub fn diagnostics(program: &php_ast::Program, interner: &Interner) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for_each_region(&program.stmts, interner, |scope, region| {
        let imports = region_imports(region, interner);

        // Duplicate imports: the same alias used twice for the same symbol kind.
        let mut seen: Vec<(UseKind, String)> = Vec::new();
        for imp in &imports {
            let key = (imp.kind, imp.fold());
            if seen.contains(&key) {
                out.push(
                    Diagnostic::warning(
                        imp.span,
                        format!("duplicate import: `{}` is already imported", imp.alias),
                    )
                    .with_code("duplicate-import"),
                );
            } else {
                seen.push(key);
            }
        }

        // Unused imports: an alias never referenced (as a name of its kind).
        let used = used_aliases(scope, region);
        for imp in &imports {
            if !used.contains(&(imp.kind, imp.fold())) {
                out.push(
                    Diagnostic::warning(imp.span, format!("unused import: `{}`", imp.alias))
                        .with_code("unused-import"),
                );
            }
        }
    });
    out.sort_by_key(|d| d.primary.start);
    out
}

struct Import {
    kind: UseKind,
    alias: String,
    span: Span,
}

impl Import {
    /// The alias as a lookup key: case-insensitive for classes/functions,
    /// case-sensitive for constants (matching PHP's resolution rules).
    fn fold(&self) -> String {
        fold(self.kind, &self.alias)
    }
}

/// The imports declared directly in a region, with the span of each imported
/// name (for diagnostics).
fn region_imports(stmts: &[Stmt], interner: &Interner) -> Vec<Import> {
    let mut imports = Vec::new();
    let mut add = |it: &UseItem| {
        let alias = match it.alias {
            Some(s) => interner.resolve(s).to_string(),
            None => it
                .name
                .text
                .rsplit('\\')
                .next()
                .unwrap_or(&it.name.text)
                .to_string(),
        };
        imports.push(Import {
            kind: it.kind,
            alias,
            span: it.name.span,
        });
    };
    for st in stmts {
        match &st.kind {
            StmtKind::Use(items) => items.iter().for_each(&mut add),
            StmtKind::GroupUse { items, .. } => items.iter().for_each(&mut add),
            _ => {}
        }
    }
    imports
}

/// The set of (kind, folded-alias) pairs actually referenced in the region: the
/// first segment of every non-fully-qualified name reference.
fn used_aliases(scope: &crate::Scope, stmts: &[Stmt]) -> Vec<(UseKind, String)> {
    let mut used = Vec::new();
    for r in collect_region(scope, stmts) {
        // Only unqualified / qualified names consult imports; `\Foo` and
        // `namespace\Foo` never do.
        if r.fq != NameFq::NotFq {
            continue;
        }
        // A *qualified* name's first segment is a namespace, so it credits the
        // class import table whatever the reference itself is — matching how
        // `resolve_callable` resolves it. Only an unqualified name consults the
        // table of its own kind.
        let (first, rest) = match r.name.split_once('\\') {
            Some((first, _)) => (first, true),
            None => (r.name.as_str(), false),
        };
        let kind = match r.kind {
            _ if rest => UseKind::Class,
            RefKind::Class => UseKind::Class,
            RefKind::Function => UseKind::Function,
            RefKind::Const => UseKind::Const,
        };
        let key = (kind, fold(kind, first));
        if !used.contains(&key) {
            used.push(key);
        }
    }
    used
}

fn fold(kind: UseKind, name: &str) -> String {
    match kind {
        UseKind::Const => name.to_string(),
        UseKind::Class | UseKind::Function => name.to_ascii_lowercase(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn diags(src: &str) -> Vec<(String, String)> {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors in test source");
        diagnostics(&r.program, &r.interner)
            .into_iter()
            .map(|d| (d.code.unwrap_or("").to_string(), d.message))
            .collect()
    }

    #[test]
    fn unused_import_is_reported() {
        let d = diags(
            r#"<?php
            namespace App;
            use App\Used;
            use App\Unused;
            new Used();
            "#,
        );
        assert_eq!(
            d,
            [("unused-import".into(), "unused import: `Unused`".into())]
        );
    }

    #[test]
    fn used_imports_are_clean() {
        let d = diags(
            r#"<?php
            namespace App;
            use App\Base;
            use function App\helper;
            use const App\LIMIT;
            class C extends Base { function m() { helper(); return LIMIT; } }
            "#,
        );
        assert!(d.is_empty(), "unexpected diagnostics: {d:?}");
    }

    #[test]
    fn class_import_is_used_by_a_qualified_function_call() {
        // The Guzzle shape: the class import supplies the namespace prefix for a
        // qualified function call, so it is used — and the function import that
        // would look like the match is not consulted at all.
        let d = diags(r#"<?php namespace App; use GuzzleHttp\Psr7; echo Psr7\str("x");"#);
        assert!(d.is_empty(), "qualified call must credit the import: {d:?}");
    }

    #[test]
    fn function_import_unused_by_a_qualified_call_of_the_same_name() {
        // `use function Other\helper;` does not bind `helper\x()` — that is the
        // current namespace's `helper\x`, so the import really is unused.
        let d = diags(r#"<?php namespace App; use function Other\helper; echo helper\x();"#);
        assert_eq!(
            d,
            [("unused-import".into(), "unused import: `helper`".into())]
        );
    }

    #[test]
    fn import_used_only_via_alias_case_insensitively() {
        let d = diags(r#"<?php namespace App; use App\Str; new STR();"#);
        assert!(d.is_empty(), "class import use is case-insensitive: {d:?}");
    }

    #[test]
    fn const_import_is_case_sensitive() {
        // `use const FOO` is not satisfied by a reference to `foo`.
        let d = diags(r#"<?php namespace App; use const App\FOO; echo foo;"#);
        assert_eq!(d, [("unused-import".into(), "unused import: `FOO`".into())]);
    }

    #[test]
    fn duplicate_import_is_reported() {
        let d = diags(
            r#"<?php
            namespace App;
            use App\A as X;
            use App\B as X;
            new X();
            "#,
        );
        assert!(d.iter().any(|(c, _)| c == "duplicate-import"));
    }

    #[test]
    fn function_and_class_imports_with_same_name_dont_collide() {
        // Different symbol namespaces — both used, no diagnostics.
        let d = diags(
            r#"<?php namespace App; use App\Thing; use function App\Thing; new Thing(); Thing();"#,
        );
        assert!(
            d.is_empty(),
            "class and function imports are independent: {d:?}"
        );
    }

    #[test]
    fn qualified_reference_marks_first_segment_used() {
        // `use App\Support;` used as `Support\Str` keeps the import live.
        let d = diags(r#"<?php namespace App; use App\Support; new Support\Str();"#);
        assert!(d.is_empty(), "qualified use of the import alias: {d:?}");
    }
}
