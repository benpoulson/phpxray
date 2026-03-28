//! M-T8: build a flow-sensitive **`span → Type` map** for a whole file, so rules
//! can ask "what's the type of this expression?" without each re-running
//! inference.
//!
//! Per scope (the global region, each function, each method) we build a
//! [`TypeCtx`], seed parameters (and `$this` for methods) from the reflected
//! signature, then walk the body statement-by-statement: at each statement record
//! the inferred type of every expression it contains (scope-bounded — not into
//! nested function-likes) using the *current* flow environment, then advance the
//! environment with the flow analysis. Closures/arrow-fns are left opaque for now
//! (their inner expressions resolve to `mixed`); narrowing is a later milestone.

use crate::TypeCtx;
use php_ast::{walk, Member, Program, StmtKind};
use php_intern::Interner;
use php_reflect::{reflect_class, reflect_function, ReflectionIndex};
use php_resolve::{for_each_region, Scope};
use php_types::Type;
use std::collections::HashMap;

/// Inferred type of each expression, keyed by its span (start, end).
pub type TypeMap = HashMap<(u32, u32), Type>;

fn key(span: php_span::Span) -> (u32, u32) {
    let r = span.range();
    (r.start as u32, r.end as u32)
}

/// Build the type map for one parsed file.
pub fn type_map(reflection: &ReflectionIndex, program: &Program, interner: &Interner) -> TypeMap {
    let mut map = TypeMap::new();
    for_each_region(&program.stmts, interner, |scope, region| {
        // Global scope of this region.
        record_scope(reflection, scope, interner, None, HashMap::new(), region, &mut map);
        // Every function / method declared in the region (descending into nested
        // and conditional declarations; each is its own scope).
        for st in region {
            walk::for_each_stmt_in_stmt(st, &mut |s| collect_scope(reflection, scope, interner, s, &mut map));
        }
    });
    map
}

/// If `s` declares a function or class, record types for each of its bodies in a
/// fresh scope.
fn collect_scope(reflection: &ReflectionIndex, scope: &Scope, interner: &Interner, s: &php_ast::Stmt, map: &mut TypeMap) {
    match &s.kind {
        StmtKind::Function(f) => {
            let refl = reflect_function(scope, interner, f);
            let vars = refl.params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect();
            record_scope(reflection, scope, interner, None, vars, &f.body, map);
        }
        StmtKind::Class(c) => {
            let Some(name) = c.name else { return };
            let fqn = scope.qualify(interner.resolve(name));
            let cls = reflect_class(scope, interner, &fqn, c);
            for m in &c.members {
                let Member::Method(md) = m else { continue };
                let Some(body) = &md.body else { continue };
                let mname = interner.resolve(md.name);
                let Some(mr) = cls.methods.iter().find(|x| !x.magic && x.name.eq_ignore_ascii_case(mname)) else {
                    continue;
                };
                let mut vars: HashMap<String, Type> = mr.params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect();
                vars.insert("this".to_string(), Type::Named { fqn: fqn.clone(), args: Vec::new() });
                record_scope(reflection, scope, interner, Some(fqn.clone()), vars, body, map);
            }
        }
        _ => {}
    }
}

/// Record types for the expressions in one scope's `body`, flowing the
/// environment between statements.
fn record_scope(
    reflection: &ReflectionIndex,
    scope: &Scope,
    interner: &Interner,
    class: Option<String>,
    init_vars: HashMap<String, Type>,
    body: &[php_ast::Stmt],
    map: &mut TypeMap,
) {
    let mut ctx = TypeCtx::new(reflection, scope, interner);
    ctx.class = class;
    ctx.vars = init_vars;
    for st in body {
        walk::for_each_expr_in_scope(st, &mut |e| {
            let t = ctx.infer(e);
            map.insert(key(e.span), t);
        });
        ctx.exec_stmt(st);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_ast::{Expr, ExprKind};

    /// Build the type map for `src` (parsed + self-reflected).
    fn build(src: &str) -> (TypeMap, php_parser::ParseResult) {
        let r = php_parser::parse(src);
        assert!(!r.has_errors(), "parse errors: {src}");
        let mut reflection = ReflectionIndex::new();
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
                found = Some(map.get(&k).map(|t| t.to_string()).unwrap_or_else(|| "<unmapped>".into()));
            }
        });
        found.unwrap_or_else(|| "<not found>".into())
    }

    #[test]
    fn literals() {
        assert_eq!(ty_of("<?php 42;", |e| matches!(e.kind, ExprKind::Int(_))), "int");
        assert_eq!(ty_of("<?php 'hi';", |e| matches!(&e.kind, ExprKind::Str(_))), "string");
    }

    #[test]
    fn local_carries_assigned_type_at_later_use() {
        // `$x = 'hi'; echo $x;` — the `$x` inside `echo` (a later statement) is string.
        let (map, r) = build("<?php $x = 'hi'; echo $x;");
        // Collect every `$x` Variable type in source order; the last is the echo use.
        let mut tys = Vec::new();
        walk::for_each_expr(&r.program, &mut |e| {
            if matches!(&e.kind, ExprKind::Variable(_)) {
                tys.push(map.get(&key(e.span)).map(|t| t.to_string()).unwrap_or_default());
            }
        });
        assert_eq!(tys.last().map(String::as_str), Some("string"), "echo $x should be string; got {tys:?}");
    }

    #[test]
    fn param_type_seeded() {
        // Inside the function, the use of $n is int (seeded from the signature).
        let (map, r) = build("<?php function f(int $n) { $m = $n + 1; }");
        let mut tys = Vec::new();
        walk::for_each_expr(&r.program, &mut |e| {
            if matches!(&e.kind, ExprKind::Variable(_)) {
                tys.push(map.get(&key(e.span)).map(|t| t.to_string()).unwrap_or_default());
            }
        });
        assert!(tys.contains(&"int".to_string()), "the $n use should be int; got {tys:?}");
    }

    #[test]
    fn call_return_type() {
        let src = "<?php function f(): string { return 'x'; } $r = f();";
        assert_eq!(ty_of(src, |e| matches!(&e.kind, ExprKind::Call { .. })), "string");
    }

    #[test]
    fn this_property_type() {
        let src = "<?php class C { public int $age = 0; public function m() { $a = $this->age; } }";
        assert_eq!(ty_of(src, |e| matches!(&e.kind, ExprKind::Prop { .. })), "int");
    }

    #[test]
    fn call_arguments_are_recorded() {
        // Args must be in the map (infer itself skips them) — the string literal arg.
        let src = "<?php function f(int $x) {} f('s');";
        assert_eq!(ty_of(src, |e| matches!(&e.kind, ExprKind::Str(_))), "string");
    }
}
