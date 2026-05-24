//! M-T8: build a flow-sensitive **`span → Type` map** for a whole file, so rules
//! can ask "what's the type of this expression?" without each re-running
//! inference.
//!
//! Per scope (the global region, each function, each method) we build a
//! [`TypeCtx`], seed parameters (and `$this` for methods) from the reflected
//! signature, then walk the body statement-by-statement: at each statement record
//! the inferred type of every expression it contains using the *current* flow
//! environment, then advance the environment with the flow analysis. Closure and
//! arrow bodies are recorded as child scopes, including direct callback params
//! inferred from selected built-in call sites.

use crate::TypeCtx;
use php_ast::{walk, Member, Program, StmtKind};
use php_intern::Interner;
use php_reflect::{reflect_class, reflect_function, ReflectionIndex};
use php_resolve::{for_each_region, Scope};
use php_types::Type;
use std::collections::HashMap;

/// Inferred type of each expression, keyed by its span (start, end).
pub type TypeMap = HashMap<(u32, u32), Type>;

#[cfg(test)]
fn key(span: php_span::Span) -> (u32, u32) {
    let r = span.range();
    (r.start as u32, r.end as u32)
}

/// Build the (merged native+PHPDoc) type map for one parsed file.
pub fn type_map(reflection: &ReflectionIndex, program: &Program, interner: &Interner) -> TypeMap {
    build(reflection, program, interner, false)
}

/// Build the **native**-only type map: types inferred ignoring PHPDoc (member
/// accesses use `native_ty`/`native_return`, arrays are untyped). Backs the
/// `treatPhpDocTypesAsCertain: false` native-level checking.
pub fn native_type_map(
    reflection: &ReflectionIndex,
    program: &Program,
    interner: &Interner,
) -> TypeMap {
    build(reflection, program, interner, true)
}

fn build(
    reflection: &ReflectionIndex,
    program: &Program,
    interner: &Interner,
    native: bool,
) -> TypeMap {
    let mut map = TypeMap::new();
    for_each_region(&program.stmts, interner, |scope, region| {
        // Global scope of this region.
        record_scope(
            reflection,
            scope,
            interner,
            None,
            HashMap::new(),
            native,
            region,
            &mut map,
        );
        // Every function / method declared in the region (descending into nested
        // and conditional declarations; each is its own scope).
        for st in region {
            walk::for_each_stmt_in_stmt(st, &mut |s| {
                collect_scope(reflection, scope, interner, s, native, &mut map)
            });
        }
    });
    map
}

/// The seeded local type of a parameter — native (untyped variadic → `array`) or
/// merged, depending on `native`.
fn seed_type(p: &php_reflect::ParamReflection, native: bool) -> Type {
    if !native {
        return p.local_type();
    }
    if p.variadic {
        Type::Array(None)
    } else {
        p.native_ty.clone()
    }
}

/// If `s` declares a function or class, record types for each of its bodies in a
/// fresh scope.
fn collect_scope(
    reflection: &ReflectionIndex,
    scope: &Scope,
    interner: &Interner,
    s: &php_ast::Stmt,
    native: bool,
    map: &mut TypeMap,
) {
    match &s.kind {
        StmtKind::Function(f) => {
            let refl = reflect_function(scope, interner, f);
            let vars = refl
                .params
                .iter()
                .map(|p| (p.name.clone(), seed_type(p, native)))
                .collect();
            record_scope(
                reflection, scope, interner, None, vars, native, &f.body, map,
            );
        }
        StmtKind::Class(c) => {
            let Some(name) = c.name else { return };
            let fqn = scope.qualify(interner.resolve(name));
            let cls = reflect_class(scope, interner, &fqn, c);
            for m in &c.members {
                let Member::Method(md) = m else { continue };
                let Some(body) = &md.body else { continue };
                let mname = interner.resolve(md.name);
                let Some(mr) = cls
                    .methods
                    .iter()
                    .find(|x| !x.magic && x.name.eq_ignore_ascii_case(mname))
                else {
                    continue;
                };
                let mut vars: HashMap<String, Type> = mr
                    .params
                    .iter()
                    .map(|p| (p.name.clone(), seed_type(p, native)))
                    .collect();
                vars.insert(
                    "this".to_string(),
                    Type::Named {
                        fqn: fqn.clone(),
                        args: Vec::new(),
                    },
                );
                record_scope(
                    reflection,
                    scope,
                    interner,
                    Some(fqn.clone()),
                    vars,
                    native,
                    body,
                    map,
                );
            }
        }
        _ => {}
    }
}

/// Record types for the expressions in one scope's `body`, flowing the
/// environment between statements.
#[allow(clippy::too_many_arguments)]
fn record_scope(
    reflection: &ReflectionIndex,
    scope: &Scope,
    interner: &Interner,
    class: Option<String>,
    init_vars: HashMap<String, Type>,
    native: bool,
    body: &[php_ast::Stmt],
    map: &mut TypeMap,
) {
    let mut ctx = TypeCtx::new(reflection, scope, interner);
    ctx.class = class;
    ctx.vars = init_vars;
    ctx.native = native;
    // The recording pass flows the environment statement-by-statement *and*
    // records each expression at its narrowed flow point, so expressions inside
    // `if`/`else`/loop branches are typed against the narrowed environment.
    ctx.record_block(body, map);
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_ast::{Expr, ExprKind, StmtKind};

    /// Build the type map for `src` (parsed + self-reflected).
    fn build(src: &str) -> (TypeMap, php_parser::ParseResult) {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors: {src}");
        let mut reflection = ReflectionIndex::with_builtins();
        reflection.add_file(&r.program, &r.interner);
        let map = type_map(&reflection, &r.program, &r.interner);
        (map, r)
    }

    /// The type of the first expression matching `pred`, as a string.
    fn ty_of(src: &str, pred: impl Fn(&Expr) -> bool) -> String {
        let (map, r) = build(src);
        let mut found: Option<String> = None;
        walk::for_each_expr(&r.program, &mut |e| {
            if found.is_none() && pred(e) {
                let k = key(e.span);
                found = Some(
                    map.get(&k)
                        .map(|t| t.to_string())
                        .unwrap_or_else(|| "<unmapped>".into()),
                );
            }
        });
        found.unwrap_or_else(|| "<not found>".into())
    }

    fn ty_of_last_method(src: &str, name: &str) -> String {
        let (map, r) = build(src);
        let mut found: Option<String> = None;
        walk::for_each_expr(&r.program, &mut |e| {
            let ExprKind::MethodCall {
                method: php_ast::MemberName::Ident(sym),
                ..
            } = &e.kind
            else {
                return;
            };
            if r.interner.resolve(*sym).eq_ignore_ascii_case(name) {
                found = map
                    .get(&key(e.span))
                    .map(|t| t.to_string())
                    .or_else(|| Some("<unmapped>".into()));
            }
        });
        found.unwrap_or_else(|| "<not found>".into())
    }

    fn ty_of_last_var(src: &str, name: &str) -> String {
        let (map, r) = build(src);
        let mut found: Option<String> = None;
        walk::for_each_expr(&r.program, &mut |e| {
            let ExprKind::Variable(sym) = &e.kind else {
                return;
            };
            if r.interner.resolve(*sym) == name {
                found = map
                    .get(&key(e.span))
                    .map(|t| t.to_string())
                    .or_else(|| Some("<unmapped>".into()));
            }
        });
        found.unwrap_or_else(|| "<not found>".into())
    }

    fn ty_of_last_call(src: &str, name: &str) -> String {
        let (map, r) = build(src);
        let mut found: Option<String> = None;
        walk::for_each_expr(&r.program, &mut |e| {
            let ExprKind::Call { callee, .. } = &e.kind else {
                return;
            };
            let ExprKind::Name(n) = &callee.kind else {
                return;
            };
            let tail = n
                .text
                .trim_start_matches('\\')
                .rsplit('\\')
                .next()
                .unwrap_or(&n.text);
            if tail.eq_ignore_ascii_case(name) {
                found = map
                    .get(&key(e.span))
                    .map(|t| t.to_string())
                    .or_else(|| Some("<unmapped>".into()));
            }
        });
        found.unwrap_or_else(|| "<not found>".into())
    }

    fn ty_of_last_static_call(src: &str, name: &str) -> String {
        let (map, r) = build(src);
        let mut found: Option<String> = None;
        walk::for_each_expr(&r.program, &mut |e| {
            let ExprKind::StaticCall {
                method: php_ast::MemberName::Ident(sym),
                ..
            } = &e.kind
            else {
                return;
            };
            if r.interner.resolve(*sym).eq_ignore_ascii_case(name) {
                found = map
                    .get(&key(e.span))
                    .map(|t| t.to_string())
                    .or_else(|| Some("<unmapped>".into()));
            }
        });
        found.unwrap_or_else(|| "<not found>".into())
    }

    #[test]
    fn literals() {
        assert_eq!(
            ty_of("<?php 42;", |e| matches!(e.kind, ExprKind::Int(_))),
            "42"
        );
        assert_eq!(
            ty_of("<?php 'hi';", |e| matches!(&e.kind, ExprKind::Str(_))),
            "'hi'"
        );
    }

    #[test]
    fn local_carries_assigned_type_at_later_use() {
        // `$x = 'hi'; echo $x;` — the `$x` inside `echo` (a later statement) is string.
        let (map, r) = build("<?php $x = 'hi'; echo $x;");
        // Collect every `$x` Variable type in source order; the last is the echo use.
        let mut tys = Vec::new();
        walk::for_each_expr(&r.program, &mut |e| {
            if matches!(&e.kind, ExprKind::Variable(_)) {
                tys.push(
                    map.get(&key(e.span))
                        .map(|t| t.to_string())
                        .unwrap_or_default(),
                );
            }
        });
        assert_eq!(
            tys.last().map(String::as_str),
            Some("'hi'"),
            "echo $x should be the literal; got {tys:?}"
        );
    }

    #[test]
    fn param_type_seeded() {
        // Inside the function, the use of $n is int (seeded from the signature).
        let (map, r) = build("<?php function f(int $n) { $m = $n + 1; }");
        let mut tys = Vec::new();
        walk::for_each_expr(&r.program, &mut |e| {
            if matches!(&e.kind, ExprKind::Variable(_)) {
                tys.push(
                    map.get(&key(e.span))
                        .map(|t| t.to_string())
                        .unwrap_or_default(),
                );
            }
        });
        assert!(
            tys.contains(&"int".to_string()),
            "the $n use should be int; got {tys:?}"
        );
    }

    #[test]
    fn call_return_type() {
        let src = "<?php function f(): string { return 'x'; } $r = f();";
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Call { .. })),
            "string"
        );
    }

    #[test]
    fn this_property_type() {
        let src = "<?php class C { public int $age = 0; public function m() { $a = $this->age; } }";
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Prop { .. })),
            "int"
        );
    }

    #[test]
    fn call_arguments_are_recorded() {
        // Args must be in the map (infer itself skips them) — the string literal arg.
        let src = "<?php function f(int $x) {} f('s');";
        assert_eq!(ty_of(src, |e| matches!(&e.kind, ExprKind::Str(_))), "'s'");
    }

    #[test]
    fn closure_param_types_inner_method_property_and_index() {
        let src = r#"<?php
        class Box {
            /** @var list<string> */
            public array $items = [];
            public function label(): string {}
        }
        function f(): void {
            $cb = function (Box $b): void {
                $b->label();
                $b->items[0];
            };
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Prop { .. })),
            "list<string>"
        );
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Index { .. })),
            "string"
        );
    }

    #[test]
    fn arrow_param_types_inner_method_property_and_index() {
        let src = r#"<?php
        class Box {
            /** @var list<string> */
            public array $items = [];
            public function label(): string {}
        }
        function f(): void {
            $cb = fn(Box $b) => [$b->label(), $b->items[0]];
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Prop { .. })),
            "list<string>"
        );
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Index { .. })),
            "string"
        );
    }

    #[test]
    fn closure_use_captures_narrowed_outer_type() {
        let src = r#"<?php
        class Box { public function label(): string {} }
        function f(object $x): void {
            if ($x instanceof Box) {
                $cb = function () use ($x): void {
                    $x->label();
                };
            }
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
    }

    #[test]
    fn arrow_auto_captures_outer_type() {
        let src = r#"<?php
        class Box { public function label(): string {} }
        function f(): void {
            $b = new Box();
            $cb = fn() => $b->label();
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
    }

    #[test]
    fn non_static_closure_preserves_this_static_closure_does_not() {
        let non_static = r#"<?php
        class Box { public function label(): string {} }
        class C {
            public Box $box;
            public function f(): void {
                $cb = function (): void { $this->box->label(); };
            }
        }
        "#;
        assert_eq!(ty_of_last_method(non_static, "label"), "string");

        let static_closure = r#"<?php
        class Box { public function label(): string {} }
        class C {
            public Box $box;
            public function f(): void {
                $cb = static function (): void { $this->box->label(); };
            }
        }
        "#;
        assert_eq!(ty_of_last_method(static_closure, "label"), "mixed");
    }

    #[test]
    fn non_static_arrow_preserves_this_static_arrow_does_not() {
        let non_static = r#"<?php
        class Box { public function label(): string {} }
        class C {
            public Box $box;
            public function f(): void {
                $cb = fn() => $this->box->label();
            }
        }
        "#;
        assert_eq!(ty_of_last_method(non_static, "label"), "string");

        let static_arrow = r#"<?php
        class Box { public function label(): string {} }
        class C {
            public Box $box;
            public function f(): void {
                $cb = static fn() => $this->box->label();
            }
        }
        "#;
        assert_eq!(ty_of_last_method(static_arrow, "label"), "mixed");
    }

    #[test]
    fn nested_closure_and_arrow_bodies_are_mapped() {
        let src = r#"<?php
        class Box { public function label(): string {} }
        function f(): void {
            $b = new Box();
            $outer = function () use ($b): void {
                $inner = fn() => $b->label();
            };
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
    }

    #[test]
    fn array_map_infers_arrow_param_from_list_value() {
        let src = r#"<?php
        class User { public function label(): string {} }
        /** @param list<User> $users */
        function f(array $users): void {
            array_map(fn($u) => $u->label(), $users);
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
    }

    #[test]
    fn array_map_infers_multiple_callback_params() {
        let src = r#"<?php
        class User { public function label(): string {} }
        class Team { public function id(): int {} }
        /**
         * @param list<User> $users
         * @param list<Team> $teams
         */
        function f(array $users, array $teams): void {
            array_map(fn($u, $t) => [$u->label(), $t->id()], $users, $teams);
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
        assert_eq!(ty_of_last_method(src, "id"), "int");
    }

    #[test]
    fn array_filter_infers_value_key_and_both_modes() {
        let src = r#"<?php
        class User { public function label(): string {} }
        /** @param array<string, User> $users */
        function f(array $users): void {
            array_filter($users, fn($u) => $u->label());
            array_filter($users, fn($k) => $k, ARRAY_FILTER_USE_KEY);
            array_filter($users, fn($u, $k) => [$u->label(), $k], ARRAY_FILTER_USE_BOTH);
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
        assert_eq!(ty_of_last_var(src, "k"), "string");
    }

    #[test]
    fn array_walk_infers_value_key_and_user_arg() {
        let src = r#"<?php
        class User { public function label(): string {} }
        /** @param array<string, User> $users */
        function f(array $users): void {
            array_walk($users, function ($u, $k, $prefix): void {
                $u->label();
                $k;
                $prefix;
            }, 'p');
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
        assert_eq!(ty_of_last_var(src, "k"), "string");
        assert_eq!(ty_of_last_var(src, "prefix"), "'p'");
    }

    #[test]
    fn sort_callbacks_infer_value_and_key_comparators() {
        let src = r#"<?php
        class User { public function label(): string {} }
        /** @param array<string, User> $users */
        function f(array $users): void {
            usort($users, fn($a, $b) => $a->label() <=> $b->label());
            uasort($users, fn($a, $b) => $a->label() <=> $b->label());
            uksort($users, fn($ka, $kb) => $ka <=> $kb);
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "string");
        assert_eq!(ty_of_last_var(src, "ka"), "string");
        assert_eq!(ty_of_last_var(src, "kb"), "string");
    }

    #[test]
    fn preg_replace_callback_infers_matches_array() {
        let src = r#"<?php
        function f(string $s): void {
            preg_replace_callback('/x/', fn($matches) => $matches[0], $s);
        }
        "#;
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Index { .. })),
            "string"
        );
    }

    #[test]
    fn explicit_callback_param_hint_is_not_overridden() {
        let src = r#"<?php
        class User { public function label(): string {} }
        /** @param list<User> $users */
        function f(array $users): void {
            array_map(fn(string $u) => $u, $users);
        }
        "#;
        assert_eq!(ty_of_last_var(src, "u"), "string");
    }

    #[test]
    fn user_function_named_array_map_does_not_infer_callback_params() {
        let src = r#"<?php
        namespace App;
        function array_map($callback, $array): void {}
        class User { public function label(): string {} }
        /** @param list<User> $users */
        function f(array $users): void {
            array_map(fn($u) => $u->label(), $users);
        }
        "#;
        assert_eq!(ty_of_last_method(src, "label"), "mixed");
    }

    #[test]
    fn userland_function_template_binds_direct_argument() {
        let src = r#"<?php
        class User {}
        /**
         * @template T
         * @param T $x
         * @return T
         */
        function id($x) {}
        function f(User $u): void {
            id($u);
        }
        "#;
        assert_eq!(ty_of_last_call(src, "id"), "User");
    }

    #[test]
    fn userland_function_template_binds_list_element() {
        let src = r#"<?php
        class User {}
        /**
         * @template T
         * @param list<T> $items
         * @return T
         */
        function first(array $items) {}
        /** @param list<User> $users */
        function f(array $users): void {
            first($users);
        }
        "#;
        assert_eq!(ty_of_last_call(src, "first"), "User");
    }

    #[test]
    fn repeated_template_bindings_union_observations() {
        let src = r#"<?php
        /**
         * @template T
         * @param T $a
         * @param T $b
         * @return T
         */
        function either($a, $b) {}
        either(1, 'x');
        "#;
        assert_eq!(ty_of_last_call(src, "either"), "1|'x'");
    }

    #[test]
    fn mixed_template_argument_stays_lenient() {
        let src = r#"<?php
        /**
         * @template T
         * @param T $x
         * @return T
         */
        function id($x) {}
        function f($x): void {
            id($x);
        }
        "#;
        assert_eq!(ty_of_last_call(src, "id"), "mixed");
    }

    #[test]
    fn method_level_templates_bind_for_instance_and_static_calls() {
        let src = r#"<?php
        class User {}
        class Box {
            /**
             * @template T
             * @param T $x
             * @return T
             */
            public function id($x) {}
            /**
             * @template T
             * @param T $x
             * @return T
             */
            public static function sid($x) {}
        }
        function f(Box $b, User $u): void {
            $b->id($u);
            Box::sid($u);
        }
        "#;
        assert_eq!(ty_of_last_method(src, "id"), "User");
        assert_eq!(ty_of_last_static_call(src, "sid"), "User");
    }

    #[test]
    fn array_map_return_uses_direct_callback_return_type() {
        let src = r#"<?php
        class Child {}
        class User { public function child(): Child {} }
        /** @param list<User> $users */
        function f(array $users): void {
            array_map(fn(User $u) => $u->child(), $users);
        }
        "#;
        assert_eq!(ty_of_last_call(src, "array_map"), "list<Child>");
    }

    #[test]
    fn array_key_value_and_column_returns_preserve_precision() {
        let src = r#"<?php
        class User {}
        /**
         * @param array<string, User> $users
         * @param list<array{id: int, name: string}> $rows
         */
        function f(array $users, array $rows): void {
            array_keys($users);
            array_values($users);
            array_column($rows, 'name');
            array_column($rows, 'name', 'id');
        }
        "#;
        assert_eq!(ty_of_last_call(src, "array_keys"), "list<string>");
        assert_eq!(ty_of_last_call(src, "array_values"), "list<User>");
        let (map, r) = build(src);
        let mut columns = Vec::new();
        walk::for_each_expr(&r.program, &mut |e| {
            let ExprKind::Call { callee, .. } = &e.kind else {
                return;
            };
            let ExprKind::Name(n) = &callee.kind else {
                return;
            };
            if n.text.eq_ignore_ascii_case("array_column") {
                columns.push(map.get(&key(e.span)).unwrap().to_string());
            }
        });
        assert_eq!(columns, ["list<string>", "array<int, string>"]);
    }

    #[test]
    fn builtin_class_templates_substitute_through_extends() {
        let src = r#"<?php
        class User {}
        /** @extends \ArrayObject<int, User> */
        class Users extends \ArrayObject {}
        function f(Users $users): void {
            $users->offsetGet(0);
        }
        "#;
        assert_eq!(ty_of_last_method(src, "offsetGet"), "User|null");
    }

    #[test]
    fn instanceof_branch_narrows_receiver_in_type_map() {
        // The receiver of a property fetch inside an `instanceof` branch must be
        // recorded as the narrowed concrete class, not the bare interface — this
        // is the type-map narrowing-into-branches fix.
        let src = "<?php \
            interface I {} \
            class C implements I { public int $n = 0; } \
            function f(I $o) { if ($o instanceof C) { $r = $o->n; } }";
        // The `$o` receiver inside the branch is `C` (was `I` before the fix).
        let (map, r) = build(src);
        let mut found = None;
        walk::for_each_expr(&r.program, &mut |e| {
            if let ExprKind::Prop { base, .. } = &e.kind {
                if found.is_none() {
                    found = map.get(&key(base.span)).map(|t| t.to_string());
                }
            }
        });
        assert_eq!(found.as_deref(), Some("C"), "receiver should narrow to C");
    }

    #[test]
    fn property_receiver_narrows_after_guard() {
        // `$this->x` narrows after a null guard (property-place narrowing), so the
        // post-guard use is the non-null type, not `?Foo`.
        let src = "<?php class Foo { public function f(): void {} } \
            class C { private ?Foo $x = null; \
                public function m() { if ($this->x === null) { return; } $r = $this->x; } }";
        // The `$this->x` in `$r = $this->x;` is `Foo` (null stripped).
        let (map, r) = build(src);
        let mut tys = Vec::new();
        walk::for_each_expr(&r.program, &mut |e| {
            if let ExprKind::Prop {
                base,
                name: php_ast::MemberName::Ident(_),
                ..
            } = &e.kind
            {
                if matches!(&base.kind, ExprKind::Variable(_)) {
                    tys.push(
                        map.get(&key(e.span))
                            .map(|t| t.to_string())
                            .unwrap_or_default(),
                    );
                }
            }
        });
        // The last `$this->x` (the read in `$r = $this->x`) is narrowed to Foo.
        assert_eq!(tys.last().map(String::as_str), Some("Foo"), "got {tys:?}");
    }

    #[test]
    fn ternary_branch_narrows_even_when_nested() {
        // `null !== $x->d ? f($x->d) : ''` inside a concat — the then-branch sees
        // `$x->d` non-null. Tests both ternary narrowing and that it applies to a
        // ternary nested inside another expression (the recursion in rec_here).
        let src = "<?php class N { public ?N $d = null; } \
            class P { public function p(N $n): string { return ''; } \
                public function f(N $x): string { return 'a' . (null !== $x->d ? $this->p($x->d) : ''); } }";
        // The `$x->d` argument to p() is narrowed to N (non-null).
        let (map, r) = build(src);
        let mut last = None;
        walk::for_each_expr(&r.program, &mut |e| {
            if let ExprKind::MethodCall { args, .. } = &e.kind {
                if let Some(a) = args.first() {
                    last = map.get(&key(a.value.span)).map(|t| t.to_string());
                }
            }
        });
        assert_eq!(last.as_deref(), Some("N"), "ternary arg should narrow to N");
    }

    #[test]
    fn max_of_ints_is_int() {
        let src = "<?php function f(int $a, int $b): bool { return max($a, $b) === 0; }";
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Call { .. })),
            "int"
        );
    }

    #[test]
    fn array_values_preserves_element_type() {
        let src = "<?php /** @param array<int, string> $a */ function f(array $a): bool { return array_values($a) === []; }";
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Call { .. })),
            "list<string>"
        );
    }

    #[test]
    fn inline_var_empty_shape_types_foreach_subject() {
        let src = "<?php $a = []; /** @var array{} $a */ foreach ($a as $v) {}";
        let (map, r) = build(src);
        let mut found = None;
        walk::for_each_stmt(&r.program, &mut |s| {
            if let StmtKind::Foreach { subject, .. } = &s.kind {
                found = map.get(&key(subject.span)).map(|t| t.to_string());
            }
        });
        assert_eq!(found.as_deref(), Some("array{}"));
    }

    #[test]
    fn inline_var_empty_shape_types_multiline_foreach_subject() {
        let src = r#"<?php
        $a = [];
        /** @var array{} $a */
        foreach ($a as $v) {}
        "#;
        let (map, r) = build(src);
        let mut found = None;
        walk::for_each_stmt(&r.program, &mut |s| {
            if let StmtKind::Foreach { subject, .. } = &s.kind {
                found = map.get(&key(subject.span)).map(|t| t.to_string());
            }
        });
        assert_eq!(found.as_deref(), Some("array{}"));
    }

    #[test]
    fn str_replace_returns_string_for_string_subject() {
        // The stub says `string|array`; a string subject yields `string`.
        let src = "<?php function f(string $s): bool { return str_replace('a', 'b', $s) === 'x'; }";
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Call { .. })),
            "string"
        );
    }

    #[test]
    fn intra_and_narrows_right_operand() {
        // `$x instanceof A && $x->n` — the right operand sees $x narrowed to A.
        let src = "<?php interface I {} class A implements I { public int $n = 0; } \
            function f(I $x): bool { return $x instanceof A && $x->n > 0; }";
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Prop { .. })),
            "int"
        );
    }

    #[test]
    fn intra_and_narrows_property_receiver() {
        // The symfony pattern: `$this->dep instanceof A && $this->dep->n`.
        let src = "<?php interface I {} class A implements I { public int $n = 0; } \
            class C { private I $dep; \
                public function m(): bool { return $this->dep instanceof A && $this->dep->n > 0; } }";
        // The inner `$this->dep` receiver (base of `->n`) narrows to A.
        let (map, r) = build(src);
        let mut found = None;
        walk::for_each_expr(&r.program, &mut |e| {
            if let ExprKind::Prop {
                base,
                name: php_ast::MemberName::Ident(_),
                ..
            } = &e.kind
            {
                if matches!(&base.kind, ExprKind::Prop { .. }) && found.is_none() {
                    found = map.get(&key(base.span)).map(|t| t.to_string());
                }
            }
        });
        assert_eq!(
            found.as_deref(),
            Some("A"),
            "inner $this->dep should narrow to A"
        );
    }

    #[test]
    fn property_instanceof_narrows_in_branch() {
        let src = "<?php interface I {} class A implements I { public int $n = 0; } \
            class C { private I $dep; \
                public function m() { if ($this->dep instanceof A) { $r = $this->dep->n; } } }";
        assert_eq!(
            ty_of(
                src,
                |e| matches!(&e.kind, ExprKind::Prop { name: php_ast::MemberName::Ident(_), base, .. } if matches!(&base.kind, ExprKind::Prop{..}))
            ),
            "int"
        );
    }

    #[test]
    fn narrowed_property_type_is_recorded() {
        // And the property fetch itself resolves through the narrowed class.
        let src = "<?php \
            interface I {} \
            class C implements I { public int $n = 0; } \
            function f(I $o) { if ($o instanceof C) { $r = $o->n; } }";
        assert_eq!(
            ty_of(src, |e| matches!(&e.kind, ExprKind::Prop { .. })),
            "int"
        );
    }

    #[test]
    fn first_class_method_callable_is_callable() {
        let src = r#"<?php
        class C {
            public function cb(): bool { return true; }
            public function f(): void { $this->cb(...); }
        }
        "#;
        assert_eq!(ty_of_last_method(src, "cb"), "callable(): bool");
    }

    #[test]
    fn inline_var_return_overrides_return_expression_type() {
        let src = r#"<?php
        interface ResponseInterface {}
        class C {
            public function getResponse(): ?ResponseInterface {}
            public function f(): ResponseInterface {
                /** @var ResponseInterface */
                return $this->getResponse();
            }
        }
        "#;
        assert_eq!(ty_of_last_method(src, "getResponse"), "ResponseInterface");
    }

    #[test]
    fn inline_var_assignment_binds_named_variable_after_assignment() {
        let src = r#"<?php
        interface NumberInterface {}
        class IntegerObject implements NumberInterface { public function toHexadecimal(): string {} }
        function make(): NumberInterface {}
        function f(): void {
            /** @var IntegerObject $uuidTime */
            $uuidTime = make();
            $uuidTime->toHexadecimal();
        }
        "#;
        assert_eq!(ty_of_last_method(src, "toHexadecimal"), "string");
    }

    #[test]
    fn repeated_no_arg_method_call_is_narrowed_after_instanceof() {
        let src = r#"<?php
        interface StreamInterface {}
        class MultipartStream implements StreamInterface { public function getBoundary(): string {} }
        class Request { public function getBody(): StreamInterface {} }
        function f(Request $request): void {
            if ($request->getBody() instanceof MultipartStream) {
                $request->getBody()->getBoundary();
            }
        }
        "#;
        assert_eq!(ty_of_last_method(src, "getBoundary"), "string");
    }
}
