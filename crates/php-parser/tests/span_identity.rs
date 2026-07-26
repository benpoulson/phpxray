//! The span-identity invariant: **no two distinct expression nodes may share a
//! byte-identical span.**
//!
//! Node identity is span-derived today (`php_span::NodeKey`), so two nodes with
//! the same span are indistinguishable to every span-keyed map — most visibly
//! `php_infer`'s type map, where the later-recorded node's type silently wins.
//! A wrapper node that consumes no extra source text is the usual way to break
//! this; the fix is to give the wrapper the wider span it actually covers (e.g.
//! including a closing delimiter) or to give the child the tighter one.
//!
//! Two known-benign exemptions are encoded below. Everything else is a bug
//! against the invariant.

use php_ast::{walk, Expr, ExprKind};
use std::collections::HashMap;

/// Nodes that legitimately share a parent's span.
///
/// `Error` nodes are synthesized during recovery and carry whatever span the
/// failed construct had — they are not real nodes and nothing keys types on
/// them.
fn exempt(e: &Expr) -> bool {
    matches!(e.kind, ExprKind::Error)
}

/// Every `(span, kind-name)` pair in `src`, for reporting collisions readably.
fn collisions(src: &str) -> Vec<String> {
    let r = php_parser::parse(src);
    let mut seen: HashMap<(u32, u32), &'static str> = HashMap::new();
    let mut bad = Vec::new();
    walk::for_each_expr(&r.program, &mut |e| {
        if exempt(e) {
            return;
        }
        let key = (e.span.start, e.span.end);
        let name = kind_name(e);
        match seen.get(&key) {
            Some(prev) => bad.push(format!("{}..{} shared by {prev} and {name}", key.0, key.1)),
            None => {
                seen.insert(key, name);
            }
        }
    });
    bad
}

fn kind_name(e: &Expr) -> &'static str {
    match &e.kind {
        ExprKind::Variable(_) => "Variable",
        ExprKind::VariableVariable(_) => "VariableVariable",
        ExprKind::DollarBrace(_) => "DollarBrace",
        ExprKind::Index { .. } => "Index",
        ExprKind::Paren(_) => "Paren",
        ExprKind::StaticCall { .. } => "StaticCall",
        ExprKind::StaticProp { .. } => "StaticProp",
        ExprKind::Call { .. } => "Call",
        ExprKind::MethodCall { .. } => "MethodCall",
        ExprKind::Interpolated(_) => "Interpolated",
        ExprKind::Name(_) => "Name",
        ExprKind::Str(_) => "Str",
        ExprKind::Int(_) => "Int",
        _ => "other",
    }
}

/// The two violations this invariant was written for.
#[test]
fn dollar_curly_and_static_dollar_members_have_distinct_spans() {
    // `${expr}` used to build `VariableVariable` and its `DollarBrace` wrapper
    // with byte-identical spans.
    for src in [
        r#"<?php $x = "${$name}";"#,
        r#"<?php $x = "${name}";"#,
        r#"<?php $x = "${name[0]}";"#,
        r#"<?php ${$a . $b} = 1;"#,
    ] {
        assert!(
            collisions(src).is_empty(),
            "span collision in {src}: {:?}",
            collisions(src)
        );
    }

    // `Class::$$x()` synthesized its `VariableVariable` with the span of the
    // WHOLE expression, so it covered the class name.
    let src = "<?php Foo::$$x();";
    assert!(
        collisions(src).is_empty(),
        "span collision in {src}: {:?}",
        collisions(src)
    );
    let r = php_parser::parse(src);
    let mut vv_span = None;
    let mut call_span = None;
    walk::for_each_expr(&r.program, &mut |e| match &e.kind {
        ExprKind::VariableVariable(_) => vv_span = Some(e.span),
        ExprKind::StaticCall { .. } => call_span = Some(e.span),
        _ => {}
    });
    let (vv, call) = (
        vv_span.expect("a VariableVariable"),
        call_span.expect("a StaticCall"),
    );
    assert!(
        vv.start > call.start,
        "the member's VariableVariable must start after the class name: vv={vv:?} call={call:?}"
    );
    // `Foo::` is 5 bytes past `<?php `, so the `$$` starts at 11.
    assert_eq!(vv.start, 11, "expected the span to start at the `$$`");
}

/// A broad sweep over constructs that nest wrappers, as a standing audit.
#[test]
fn representative_sources_uphold_the_invariant() {
    let sources = [
        "<?php $a = (((1)));",
        "<?php $a = $b['c']['d'];",
        "<?php $a = $this->b->c();",
        "<?php $a = Foo::BAR;",
        "<?php $a = Foo::$bar;",
        "<?php $a = $$x;",
        "<?php $a = ${'x'};",
        r#"<?php $a = "text $b[0] {$c->d} ${e} end";"#,
        "<?php $a = fn($x) => $x + 1;",
        "<?php $a = function () use ($b) { return $b; };",
        "<?php $a = match(true) { default => 1 };",
        "<?php $a = new class { public int $p = 1; };",
        "<?php $a = [1, 2, ...$rest];",
        "<?php $a = $b ?? $c ?: $d;",
        "<?php $a = strlen(...);",
        "<?php [$a, [$b, $c]] = $d;",
        "<?php $a = <<<EOT\n  $b\n  EOT;",
        "<?php $a = -$b ** 2;",
        "<?php $a = (int) $b;",
        "<?php $a = clone $b;",
    ];
    for src in sources {
        let bad = collisions(src);
        assert!(bad.is_empty(), "span collision in {src}: {bad:?}");
    }
}

/// `Error` nodes must mean "invalid source", nothing else.
///
/// First-class-callable syntax (`f(...)`) used to plant an `ExprKind::Error`
/// inside perfectly valid code, so any pass treating `Error` as parse damage —
/// or trying to type an argument's value — was wrong on every such call.
#[test]
fn first_class_callables_contain_no_error_nodes() {
    for src in [
        "<?php $f = strlen(...);",
        "<?php $f = $obj->method(...);",
        "<?php $f = Foo::bar(...);",
        "<?php array_map(strlen(...), $xs);",
    ] {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "{src} should parse cleanly");
        let mut errors = 0;
        let mut placeholders = 0;
        walk::for_each_expr(&r.program, &mut |e| match e.kind {
            ExprKind::Error => errors += 1,
            ExprKind::CallablePlaceholder => placeholders += 1,
            _ => {}
        });
        assert_eq!(errors, 0, "{src} planted an Error node in valid code");
        assert_eq!(placeholders, 1, "{src} should have exactly one placeholder");
    }

    // Genuinely invalid source still produces Error nodes.
    let bad = php_parser::parse("<?php $x = ;");
    assert!(bad.has_errors());
}

/// Valid PHP must not produce parse errors. Each of these is `php -l`-clean but
/// used to hit a gap in a lookahead set or a bracket-matching scan.
#[test]
fn accepted_by_php_parses_cleanly() {
    for src in [
        // A bare `yield` before `:` or `=>` — neither token can start an
        // expression, so the operand lookahead has to treat them as terminators.
        "<?php function g() { $a = 1; $b = $a ? yield : 2; }",
        "<?php function g() { $x = [yield => 1]; }",
        "<?php function g() { switch (1) { case yield: break; } }",
        // The keyed form still parses (the operand is read first).
        "<?php function g() { $c = yield 5 => 6; }",
        // An attribute inside a `clone` argument list: `#[` opens a bracket the
        // call-vs-construct scan must balance, or its `]` ends the scan early.
        "<?php $c = clone($a, $b);",
        "<?php $c = clone(#[A] fn() => 1, $x);",
    ] {
        let r = php_parser::parse(src);
        assert!(
            !r.has_errors(),
            "{src} should parse cleanly, got {:?}",
            r.diagnostics
        );
    }
}

/// A doc-comment attaches across whitespace, comments and attributes, but not
/// across real code.
#[test]
fn doc_comments_attach_through_comment_runs() {
    let doc_of = |src: &str| {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors in: {src}");
        r.program.stmts.iter().find_map(|s| match &s.kind {
            php_ast::StmtKind::Function(f) => Some(f.doc.is_some()),
            _ => None,
        })
    };
    for src in [
        "<?php /** @return int */ function f() {}",
        "<?php /** @return int */\n\nfunction f() {}",
        // The everyday shape that used to lose its types.
        "<?php /** @return int */\n// note\nfunction f() {}",
        "<?php /** @return int */\n# note\nfunction f() {}",
        "<?php /** @return int */\n/* note */\nfunction f() {}",
        "<?php /** @return int */\n// one\n/* two */\n// three\nfunction f() {}",
        "<?php /** @return int */\n#[Attr]\nfunction f() {}",
    ] {
        assert_eq!(doc_of(src), Some(true), "should attach: {src}");
    }
    for src in [
        // Real code intervened: the block is not documenting `f`.
        "<?php /** @return int */\n$x = 1;\nfunction f() {}",
        "<?php /** @return int */\nconst A = 1;\nfunction f() {}",
        // Leaving PHP is not trivia.
        "<?php /** @return int */ ?>\n<p>x</p>\n<?php function f() {}",
    ] {
        assert_eq!(doc_of(src), Some(false), "should not attach: {src}");
    }
}

/// An interpolated binary string must reach the AST. Letting the `b` prefix lex
/// as a name dropped the whole literal: `$y = b"a$x";` parsed as `$y = b`.
#[test]
fn interpolated_binary_strings_reach_the_ast() {
    let r = php_parser::parse("<?php $x = 1; $y = b\"a$x\";");
    assert!(!r.has_errors(), "{:?}", r.diagnostics);
    let mut interps = 0;
    let mut names = 0;
    walk::for_each_expr(&r.program, &mut |e| match &e.kind {
        ExprKind::Interpolated(_) => interps += 1,
        ExprKind::Name(_) => names += 1,
        _ => {}
    });
    assert_eq!(interps, 1, "the binary string should be an interpolation");
    assert_eq!(names, 0, "the `b` prefix must not become a constant name");
}

/// An attribute in a position PHP rejects must produce a diagnostic, not vanish.
///
/// Silently dropping it accepted invalid code *and* left the AST claiming no
/// attribute was written — a lie to any attribute-scanning rule.
#[test]
fn misplaced_attributes_are_reported() {
    for src in [
        "<?php #[A] new Foo();",
        "<?php $x = #[A] 1 + 2;",
        "<?php $x = new #[A] Foo();",
    ] {
        let r = php_parser::parse(src);
        assert!(r.has_errors(), "{src} should be rejected");
    }
    // The three positions PHP does allow stay clean.
    for src in [
        "<?php #[A] function () {};",
        "<?php #[A] fn() => 1;",
        "<?php $x = new #[A] class {};",
        "<?php $x = new #[A] readonly class {};",
    ] {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "{src} should parse cleanly: {:?}", r.diagnostics);
    }
}
