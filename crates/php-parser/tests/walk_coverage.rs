//! `php_ast::walk` coverage: every AST node kind that carries attributes must
//! have its attribute arguments traversed.
//!
//! Regression: `walk_attrs` was reachable from only two of the eleven
//! attribute-carrying node kinds (params and class declarations), so expressions
//! inside `#[Attr(Foo::BAR)]` on functions, methods, properties, class
//! constants, enum cases, property hooks, closures, arrow fns and top-level
//! consts were invisible to `for_each_expr` — existence and argument checks
//! silently did not run there, and *asymmetrically*.

use php_ast::{walk, ExprKind};

/// Does `for_each_expr` (crossing scopes) reach a `Marker::HERE` class constant
/// placed inside an attribute in `src`?
fn visits_marker(src: &str) -> bool {
    let r = php_parser::parse(src);
    assert!(!r.has_errors(), "parse errors in: {src}");
    let mut found = false;
    walk::for_each_expr(&r.program, &mut |e| {
        if let ExprKind::ClassConst {
            name: php_ast::MemberName::Ident(sym),
            ..
        } = &e.kind
        {
            found |= r.interner.resolve(*sym) == "HERE";
        }
    });
    found
}

#[test]
fn attribute_arguments_are_walked_on_every_node_kind() {
    let cases: &[(&str, &str)] = &[
        ("class", "<?php #[A(Marker::HERE)] class C {}"),
        ("function", "<?php #[A(Marker::HERE)] function f() {}"),
        ("param", "<?php function f(#[A(Marker::HERE)] $p) {}"),
        (
            "method",
            "<?php class C { #[A(Marker::HERE)] public function m() {} }",
        ),
        (
            "property",
            "<?php class C { #[A(Marker::HERE)] public $p; }",
        ),
        (
            "class const",
            "<?php class C { #[A(Marker::HERE)] const K = 1; }",
        ),
        ("enum case", "<?php enum E { #[A(Marker::HERE)] case One; }"),
        (
            "property hook",
            "<?php class C { public $p { #[A(Marker::HERE)] get => 1; } }",
        ),
        (
            "promoted-param hook attribute",
            "<?php class C { public function __construct(public int $p = 1 { #[A(Marker::HERE)] get => 1; }) {} }",
        ),
        (
            "promoted-param hook body",
            "<?php class C { public function __construct(public int $p = 1 { get => Marker::HERE; }) {} }",
        ),
        ("closure", "<?php $f = #[A(Marker::HERE)] function () {};"),
        ("arrow fn", "<?php $f = #[A(Marker::HERE)] fn () => 1;"),
        ("top-level const", "<?php #[A(Marker::HERE)] const K = 1;"),
    ];
    for (label, src) in cases {
        assert!(
            visits_marker(src),
            "for_each_expr did not visit the attribute argument on a {label}: {src}"
        );
    }
}

/// The in-scope walker (`cross = false`) stops at function-like boundaries. It
/// must keep doing so — the attribute additions ride the existing `if cross`
/// arms, matching the pre-existing param/class precedent.
#[test]
fn in_scope_walker_still_stops_at_scope_boundaries() {
    let r = php_parser::parse("<?php #[A(Marker::HERE)] function f() {}");
    assert!(!r.has_errors());
    let mut found = false;
    for st in &r.program.stmts {
        walk::for_each_expr_in_scope(st, &mut |e| {
            if let ExprKind::ClassConst {
                name: php_ast::MemberName::Ident(sym),
                ..
            } = &e.kind
            {
                found |= r.interner.resolve(*sym) == "HERE";
            }
        });
    }
    assert!(
        !found,
        "the in-scope walker must not descend into a declaration"
    );
}
