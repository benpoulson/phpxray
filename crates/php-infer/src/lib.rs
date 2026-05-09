//! M-T4: **expression type inference**.
//!
//! Given a typing context — the project [`ReflectionIndex`], the active name
//! resolution [`Scope`], the enclosing class, and the known types of local
//! variables — [`TypeCtx::infer`] computes the [`Type`] of an expression. This
//! is the first piece of the type *system* (everything before it resolved
//! *declarations*); the rules engine builds on it to flag type errors.
//!
//! The inference here is **expression-local and flow-insensitive**: variable
//! types come from the pre-seeded environment, not from tracking assignments
//! along a path (a later milestone adds the statement-level dataflow). Anything
//! we can't pin down resolves to [`Type::Mixed`] — inference is best-effort and
//! never panics.

mod assign;
mod const_eval;
mod definedness;
mod flow;
mod type_map;

pub use assign::{assignable_certain, is_assignable, is_castable_to_string, native_shape};
pub use const_eval::{eval_const, ConstVal};
pub use definedness::{undefined_variables, UndefVar};
pub use type_map::{native_type_map, type_map, TypeMap};

use php_ast::{BinOp, CastKind, Expr, ExprKind, MemberName, Name, UnOp};
use php_intern::Interner;
use php_reflect::ReflectionIndex;
use php_resolve::{Resolution, Scope};
use php_types::Type;
use std::collections::HashMap;

/// The context an expression is typed in.
pub struct TypeCtx<'a> {
    /// Project-wide reflection (classes/functions with resolved member types).
    pub index: &'a ReflectionIndex,
    /// Name resolution for the current namespace block.
    pub scope: &'a Scope,
    /// Resolves variable/member symbols to text.
    pub interner: &'a Interner,
    /// FQN of the enclosing class, for `self`/`static`/`parent`/`$this`.
    pub class: Option<String>,
    /// Known local variable types, keyed by name (without `$`).
    pub vars: HashMap<String, Type>,
    /// Interprocedural recursion depth for per-call return inference. 0 at the top
    /// level; a callee's body is analysed at depth+1. Bounded to one level so
    /// inference can't recurse without limit (mutual recursion, deep chains).
    pub depth: u32,
    /// **Native mode**: infer using *native*-hint types only (ignore PHPDoc) —
    /// member accesses use `native_ty`/`native_return`, array literals lose their
    /// element types (native PHP `array` is untyped). Drives the native type map
    /// that backs `treatPhpDocTypesAsCertain: false` checking.
    pub native: bool,
}

impl<'a> TypeCtx<'a> {
    /// A context with no class and no known variables.
    pub fn new(index: &'a ReflectionIndex, scope: &'a Scope, interner: &'a Interner) -> Self {
        TypeCtx { index, scope, interner, class: None, vars: HashMap::new(), depth: 0, native: false }
    }

    /// Infer the type of `e`.
    pub fn infer(&self, e: &Expr) -> Type {
        match &e.kind {
            // --- literals --- (carry the value as a literal type, like phpstan, so
            // literal-union params/`@return`s and constant comparisons type-check)
            ExprKind::Int(n) => Type::LiteralInt(*n),
            ExprKind::Float(_) => Type::Float,
            ExprKind::Str(bytes) => literal_string(bytes),
            ExprKind::Interpolated(_) | ExprKind::ShellExec(_) => Type::String,

            // --- references ---
            ExprKind::Variable(sym) => self.variable(self.interner.resolve(*sym)),
            ExprKind::Name(n) => self.name_type(n),
            ExprKind::DollarBrace(inner) => self.infer(inner),
            ExprKind::VariableVariable(_) => Type::Mixed,

            // --- composite ---
            ExprKind::Array { items, .. } => self.array_type(items),
            ExprKind::Call { callee, args } => self.call_type(callee, args),
            ExprKind::MethodCall { recv, nullsafe, method, args, .. } => {
                self.method_type(recv, *nullsafe, method, args)
            }
            ExprKind::StaticCall { class, method, args } => self.static_call_type(class, method, args),
            ExprKind::New { class, .. } => self.class_type(class).unwrap_or(Type::Object),
            ExprKind::NewAnon { .. } => Type::Object,
            ExprKind::Prop { base, nullsafe, name } => {
                // A flow-narrowed property place (`$this->prop` after a guard) wins
                // over the declared property type.
                if let Some(t) = self.place_key(e).and_then(|k| self.vars.get(&k).cloned()) {
                    return t;
                }
                self.prop_type(base, *nullsafe, name)
            }
            ExprKind::StaticProp { class, name } => self.static_prop_type(class, name),
            ExprKind::ClassConst { class, name } => self.class_const_type(class, name),
            ExprKind::Index { base, index } => self.index_type(base, index.as_deref()),

            // --- operators ---
            ExprKind::Unary { op, expr } => self.unary_type(*op, expr),
            ExprKind::Binary { op, lhs, rhs } => self.binary_type(*op, lhs, rhs),
            ExprKind::Assign { rhs, .. } | ExprKind::AssignRef { rhs, .. } => self.infer(rhs),
            ExprKind::AssignOp { op, target, rhs } => self.binary_type(*op, target, rhs),
            ExprKind::Cast { kind, .. } => cast_type(*kind),
            ExprKind::Ternary { then, els, cond } => {
                // Short ternary `a ?: b` yields `a` only when `a` is truthy, so the
                // then-value is `a` with its falsy members (`null`/`false`) stripped.
                let then_ty = match then {
                    Some(t) => self.infer(t),
                    None => strip_falsy(self.infer(cond)),
                };
                Type::union(vec![then_ty, self.infer(els)])
            }
            ExprKind::Coalesce { lhs, rhs } => Type::union(vec![strip_null(self.infer(lhs)), self.infer(rhs)]),
            ExprKind::PreInc(e) | ExprKind::PreDec(e) | ExprKind::PostInc(e) | ExprKind::PostDec(e) => {
                inc_dec_type(self.infer(e))
            }
            ExprKind::Instanceof { .. } => Type::Bool,
            ExprKind::Clone(e) => self.infer(e),
            ExprKind::Print(_) => Type::Int,
            ExprKind::Isset(_) | ExprKind::Empty(_) => Type::Bool,
            ExprKind::ErrorSuppress(e) => self.infer(e),
            ExprKind::Match { arms, .. } => {
                Type::union(arms.iter().map(|a| self.infer(&a.body)).collect())
            }
            ExprKind::Paren(e) => self.infer(e),

            // --- control-flow-ish / not yet modelled ---
            ExprKind::Closure(_) | ExprKind::ArrowFn(_) => Type::Named { fqn: "Closure".into(), args: vec![] },
            ExprKind::Throw(_) | ExprKind::Exit(_) => Type::Never,
            ExprKind::Yield { .. } | ExprKind::YieldFrom(_) => Type::Mixed,
            ExprKind::Include { .. } | ExprKind::Eval(_) => Type::Mixed,
            ExprKind::Error => Type::Mixed,
            // `ExprKind` is `#[non_exhaustive]`; anything new infers as mixed.
            _ => Type::Mixed,
        }
    }

    /// The type of variable `$name`.
    fn variable(&self, name: &str) -> Type {
        if name == "this" {
            return self.class.clone().map(|fqn| Type::Named { fqn, args: vec![] }).unwrap_or(Type::Mixed);
        }
        self.vars.get(name).cloned().unwrap_or(Type::Mixed)
    }

    /// A bare name in value position: `true`/`false`/`null`, a magic constant, or
    /// a (user/built-in) constant. We don't track constant *values*, so a plain
    /// constant resolves to `mixed`.
    fn name_type(&self, n: &Name) -> Type {
        let bare = n.text.trim_start_matches('\\');
        match bare.to_ascii_lowercase().as_str() {
            "true" => return Type::True,
            "false" => return Type::False,
            "null" => return Type::Null,
            _ => {}
        }
        if let Some(t) = magic_constant(bare) {
            return t;
        }
        Type::Mixed
    }

    /// `[a, b, 'k' => c]` → `array<K, V>` with `K`/`V` the unions of the element
    /// key/value types. An empty or spread-containing literal falls back to a
    /// bare `array`.
    fn array_type(&self, items: &[php_ast::ArrayItem]) -> Type {
        // Native PHP arrays are untyped — element/shape precision is PHPDoc-level.
        if self.native {
            return Type::Array(None);
        }
        if items.is_empty() || items.iter().any(|i| i.spread) {
            return Type::Array(None);
        }
        // A literal whose every entry has a *constant* key (`['a' => …, 5 => …]`)
        // is an array shape `array{a: …, 5: …}` — the precision phpstan tracks and
        // the form user code assigns to `array{…}`-typed slots. Capped to keep
        // shapes (and their Display) bounded; beyond it, fall back to `array<K,V>`.
        const MAX_SHAPE_FIELDS: usize = 64;
        if items.len() <= MAX_SHAPE_FIELDS {
            if let Some(fields) = self.shape_fields(items) {
                return Type::Shape { fields, sealed: true };
            }
        }
        let mut keys = Vec::new();
        let mut vals = Vec::new();
        let mut all_keyless = true;
        for it in items {
            match &it.key {
                Some(k) => {
                    all_keyless = false;
                    keys.push(self.infer(k));
                }
                None => keys.push(Type::Int), // list-style integer key
            }
            vals.push(it.value.as_ref().map(|v| self.infer(v)).unwrap_or(Type::Mixed));
        }
        // A literal with only positional (keyless) items is a `list<V>` — matches
        // phpstan, and is what user code assigns to `list<…>`-typed properties.
        if all_keyless {
            return Type::List(Box::new(Type::union(vals)));
        }
        Type::Array(Some(Box::new((Type::union(keys), Type::union(vals)))))
    }

    /// If *every* item of an array literal has a constant (literal string/int) key
    /// with no duplicates, return the array-shape fields. `None` otherwise (a
    /// keyless, dynamic-keyed, or duplicate-keyed literal isn't a shape).
    fn shape_fields(&self, items: &[php_ast::ArrayItem]) -> Option<Vec<php_types::ShapeField>> {
        let mut fields: Vec<php_types::ShapeField> = Vec::with_capacity(items.len());
        for it in items {
            let key = const_key(it.key.as_ref()?)?;
            if fields.iter().any(|f| f.key.as_deref() == Some(key.as_str())) {
                return None; // duplicate key — not a well-formed shape
            }
            let ty = it.value.as_ref().map(|v| self.infer(v)).unwrap_or(Type::Mixed);
            fields.push(php_types::ShapeField { key: Some(key), optional: false, ty });
        }
        Some(fields)
    }

    /// Return type of a free function call `f(...)`.
    fn call_type(&self, callee: &Expr, args: &[php_ast::Arg]) -> Type {
        let ExprKind::Name(n) = &callee.kind else { return Type::Mixed };
        // A few built-ins have argument-dependent return types that a static stub
        // can't express (it gives the worst-case union); model the common ones so
        // their result doesn't poison downstream type checks.
        let fname = n.text.trim_start_matches('\\').rsplit('\\').next().unwrap_or(&n.text).to_ascii_lowercase();
        if let Some(t) = self.dynamic_return(&fname, args) {
            return t;
        }
        match self.function_reflection(n) {
            Some(f) if self.native => f.native_return.clone(),
            Some(f) => {
                let params: Vec<String> = f.params.iter().map(|p| p.name.clone()).collect();
                let body = self.index.function_body(&f.fqn);
                self.refine_return(&f.return_type, body, &params, args, None)
            }
            None => Type::Mixed,
        }
    }

    /// Interprocedural per-call return refinement. When a callee has a body and a
    /// declared return that still admits `null`, re-derive the return type for
    /// *this* call by binding parameters to the argument types and walking the body
    /// with statically-dead branches pruned (a `?T`-returning helper that only
    /// returns null under a guard the arguments rule out yields `T` here). The body
    /// is analysed in *its own* scope (kept with it in the index) over the shared
    /// interner. Used only when the result is a sound refinement (assignable to the
    /// declared type); bounded to one interprocedural level via `depth`.
    fn refine_return(
        &self,
        declared: &Type,
        body: Option<(&[php_ast::Stmt], &Scope)>,
        params: &[String],
        args: &[php_ast::Arg],
        callee_class: Option<String>,
    ) -> Type {
        let Some((body, callee_scope)) = body else { return declared.clone() };
        // Only refine a *concrete* nullable (`?T` / `T|null`) — where pruning a
        // guarded `return null` actually tightens the type. Bare `mixed` is left be.
        let refinable = matches!(declared, Type::Nullable(_))
            || matches!(declared, Type::Union(parts) if parts.contains(&Type::Null));
        // Allow two interprocedural levels: a helper that returns `f(...)` whose own
        // nullability depends on *its* arguments (e.g. `getResolvedName` ending in
        // `FullyQualified::concat($ns, $name)`) needs the inner call refined too.
        if self.depth >= 2 || !refinable {
            return declared.clone();
        }
        let mut sub = TypeCtx {
            index: self.index,
            scope: callee_scope,
            interner: self.interner,
            class: callee_class,
            vars: HashMap::new(),
            depth: self.depth + 1,
            native: self.native,
        };
        for (name, arg) in params.iter().zip(args) {
            sub.vars.insert(name.clone(), self.infer(&arg.value));
        }
        let mut returns = Vec::new();
        sub.collect_returns(body, &mut returns);
        let collected = Type::union(returns);
        if collected != Type::Never && crate::is_assignable(self.index, &collected, declared) {
            collected
        } else {
            declared.clone()
        }
    }

    /// Collect the types of the `return <expr>` statements reachable in `stmts`,
    /// pruning `if` branches whose condition is statically known from the bound
    /// **parameter** types (so a guarded `return null` the arguments rule out is
    /// not collected). Deliberately does **not** track local assignments: a local
    /// is only ever conditionally/loop-assigned in general, and treating such an
    /// assignment as definite would unsoundly drop `null` from a `return $local`
    /// (a real false-positive source). Unknown locals infer as `mixed`, which
    /// keeps the refinement conservative — it can tighten returns built from
    /// params/`new`/literals, never from flow-dependent locals.
    fn collect_returns(&mut self, stmts: &[php_ast::Stmt], out: &mut Vec<Type>) {
        use php_ast::StmtKind as S;
        for s in stmts {
            match &s.kind {
                S::Return(Some(e)) => out.push(self.infer(e)),
                S::Block(b) => self.collect_returns(b, out),
                S::If { cond, then, elseifs, els } => {
                    self.collect_if_returns(cond, then, elseifs, els.as_deref(), out)
                }
                S::While { body, .. } | S::DoWhile { body, .. } | S::For { body, .. } | S::Foreach { body, .. } => {
                    self.collect_returns(std::slice::from_ref(body), out)
                }
                S::Switch { cases, .. } => {
                    for c in cases {
                        self.collect_returns(&c.body, out);
                    }
                }
                S::Try { body, catches, finally } => {
                    self.collect_returns(body, out);
                    for c in catches {
                        self.collect_returns(&c.body, out);
                    }
                    if let Some(f) = finally {
                        self.collect_returns(f, out);
                    }
                }
                _ => {}
            }
        }
    }

    /// Collect returns from an `if` chain, pruning statically-dead branches.
    fn collect_if_returns(
        &mut self,
        cond: &Expr,
        then: &php_ast::Stmt,
        elseifs: &[php_ast::ElseIf],
        els: Option<&php_ast::Stmt>,
        out: &mut Vec<Type>,
    ) {
        match self.static_truth(cond) {
            Some(true) => self.collect_returns(std::slice::from_ref(then), out),
            Some(false) => {
                if let Some((first, rest)) = elseifs.split_first() {
                    self.collect_if_returns(&first.cond, &first.body, rest, els, out)
                } else if let Some(e) = els {
                    self.collect_returns(std::slice::from_ref(e), out)
                }
            }
            None => {
                self.collect_returns(std::slice::from_ref(then), out);
                for ei in elseifs {
                    self.collect_returns(std::slice::from_ref(&ei.body), out);
                }
                if let Some(e) = els {
                    self.collect_returns(std::slice::from_ref(e), out);
                }
            }
        }
    }

    /// Statically evaluate a condition's truth under the current environment, for
    /// dead-branch pruning in [`collect_returns`]. Only **sound** verdicts: a
    /// `null`-comparison whose operand can't be null, `is_null`, and the boolean
    /// connectives composed from them. `None` = unknown (no pruning).
    fn static_truth(&self, cond: &Expr) -> Option<bool> {
        match &cond.kind {
            ExprKind::Paren(inner) => self.static_truth(inner),
            ExprKind::Unary { op: UnOp::Not, expr } => self.static_truth(expr).map(|b| !b),
            ExprKind::Binary { op: BinOp::BoolAnd | BinOp::LogicalAnd, lhs, rhs } => {
                match (self.static_truth(lhs), self.static_truth(rhs)) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            }
            ExprKind::Binary { op: BinOp::BoolOr | BinOp::LogicalOr, lhs, rhs } => {
                match (self.static_truth(lhs), self.static_truth(rhs)) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                }
            }
            ExprKind::Binary { op: op @ (BinOp::Identical | BinOp::Eq | BinOp::NotIdentical | BinOp::NotEq), lhs, rhs } => {
                let eq = matches!(op, BinOp::Identical | BinOp::Eq);
                // `$x === null` / `null === $x`: decided by whether the operand can be null.
                if is_null_literal(lhs) || is_null_literal(rhs) {
                    let other = if is_null_literal(lhs) { rhs } else { lhs };
                    return null_truth(&self.infer(other)).map(|n| if eq { n } else { !n });
                }
                // `$type === Foo::BAR` between two known literal ints (e.g. an enum-like
                // class constant passed as an argument): compare the values.
                if let (Type::LiteralInt(a), Type::LiteralInt(b)) = (self.infer(lhs), self.infer(rhs)) {
                    let same = a == b;
                    return Some(if eq { same } else { !same });
                }
                None
            }
            ExprKind::Call { callee, args } => {
                let ExprKind::Name(n) = &callee.kind else { return None };
                if !n.text.trim_start_matches('\\').eq_ignore_ascii_case("is_null") {
                    return None;
                }
                null_truth(&self.infer(&args.first()?.value))
            }
            _ => None,
        }
    }

    /// Argument-dependent return types for selected built-ins. Returns `None` to
    /// fall back to the stub signature.
    fn dynamic_return(&self, fname: &str, args: &[php_ast::Arg]) -> Option<Type> {
        // The string-replace family returns the *subject*'s shape: a string
        // subject yields a string, an array subject an array. The stub can only
        // say `string|array`, which then poisons every downstream string use.
        if let Some(idx) = match fname {
            "str_replace" | "str_ireplace" | "preg_replace" | "preg_replace_callback"
            | "preg_replace_callback_array" => Some(2),
            "substr_replace" => Some(0),
            _ => None,
        } {
            return match self.infer(&args.get(idx)?.value) {
                Type::String | Type::LiteralString(_) => Some(Type::String),
                Type::Array(_) | Type::List(_) => Some(Type::Array(None)),
                _ => None,
            };
        }

        // Array functions that preserve their first argument's element type — the
        // stubs return a bare `array`, losing the value type and cascading into
        // downstream `array<K,V>` argument/return mismatches.
        match fname {
            // `array_values(array<K,V>)` → `list<V>`.
            "array_values" => Some(Type::List(Box::new(self.array_value_type(args.first()?)?))),
            // These keep the value type (keys may change, but value type holds);
            // returning the input array type is correct and false-positive-safe.
            "array_filter" | "array_reverse" | "array_unique" | "array_slice" | "array_splice"
            | "array_pad" | "array_diff" | "array_intersect" => {
                match self.infer(&args.first()?.value) {
                    t @ (Type::Array(_) | Type::List(_)) => Some(t),
                    _ => None,
                }
            }
            // `max`/`min`: a single iterable arg yields its value type; otherwise
            // the union of the argument types. The stub's `int|float` otherwise
            // poisons `int`-typed uses (e.g. `str_repeat(' ', max(0, $n - $w))`).
            "max" | "min" => {
                if args.len() == 1 {
                    return self.array_value_type(args.first()?);
                }
                let tys: Vec<Type> = args.iter().map(|a| self.infer(&a.value)).collect();
                Some(Type::union(tys))
            }
            // `abs` preserves int/float.
            "abs" => match self.infer(&args.first()?.value) {
                Type::Int | Type::LiteralInt(_) => Some(Type::Int),
                Type::Float => Some(Type::Float),
                _ => None,
            },
            // `array_search($needle, $haystack)` returns the *key* of the haystack
            // (or `false`). The stub's `int|string|false` poisons int-keyed (list)
            // uses — `array_splice($list, array_search(...), …)` after `!== false`.
            "array_search" => {
                let key = self.array_key_type(args.get(1)?)?;
                Some(Type::union(vec![key, Type::False]))
            }
            // `array_key_first`/`array_key_last` return the key (or `null`).
            "array_key_first" | "array_key_last" => {
                let key = self.array_key_type(args.first()?)?;
                Some(Type::union(vec![key, Type::Null]))
            }
            // `count_chars($s, $mode)`: modes 0-2 return an array, mode 3/4 a string.
            // The stub's `array|string` poisons `strlen(count_chars($s, 3))`.
            "count_chars" => match self.infer(&args.get(1)?.value) {
                Type::LiteralInt(3) | Type::LiteralInt(4) => Some(Type::String),
                Type::LiteralInt(0..=2) => Some(Type::Array(None)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The value (element) type of an array/list argument, if known.
    fn array_value_type(&self, arg: &php_ast::Arg) -> Option<Type> {
        match self.infer(&arg.value) {
            Type::Array(Some(kv)) => Some(kv.1.clone()),
            Type::List(v) => Some(*v),
            _ => None,
        }
    }

    /// The key type of an array/list/shape argument, if known (`list` → `int`).
    fn array_key_type(&self, arg: &php_ast::Arg) -> Option<Type> {
        match self.infer(&arg.value) {
            Type::Array(Some(kv)) => Some(kv.0.clone()),
            Type::List(_) => Some(Type::Int),
            Type::Shape { fields, .. } => Some(Type::union(
                fields
                    .iter()
                    .map(|f| match &f.key {
                        Some(k) if k.parse::<i64>().is_ok() => Type::Int,
                        Some(_) => Type::String,
                        None => Type::Int,
                    })
                    .collect(),
            )),
            _ => None,
        }
    }

    /// Return type of `$recv->method(...)`.
    fn method_type(&self, recv: &Expr, nullsafe: bool, method: &MemberName, args: &[php_ast::Arg]) -> Type {
        let recv_ty = self.infer(recv);
        let Some(name) = self.member_ident(method) else { return Type::Mixed };
        let Some(fqn) = self.type_class_fqn(&recv_ty) else { return Type::Mixed };
        let ret = match self.index.find_method(&fqn, &name) {
            Some(found) if self.native => self.bind_relative(found.member.native_return, &fqn),
            Some(found) => {
                let params: Vec<String> = found.member.params.iter().map(|p| p.name.clone()).collect();
                let body = self.index.method_body(&found.declaring_class, &name);
                let refined = self.refine_return(&found.member.return_type, body, &params, args, Some(fqn.clone()));
                self.bind_relative(refined, &fqn)
            }
            None => Type::Mixed,
        };
        if nullsafe {
            ret.nullable()
        } else {
            ret
        }
    }

    /// Return type of `Class::method(...)`.
    fn static_call_type(&self, class: &Expr, method: &MemberName, args: &[php_ast::Arg]) -> Type {
        let Some(name) = self.member_ident(method) else { return Type::Mixed };
        let Some(fqn) = self.class_type(class).and_then(|t| self.type_class_fqn(&t)) else {
            return Type::Mixed;
        };
        match self.index.find_method(&fqn, &name) {
            Some(found) if self.native => self.bind_relative(found.member.native_return, &fqn),
            Some(found) => {
                let params: Vec<String> = found.member.params.iter().map(|p| p.name.clone()).collect();
                let body = self.index.method_body(&found.declaring_class, &name);
                let refined = self.refine_return(&found.member.return_type, body, &params, args, Some(fqn.clone()));
                self.bind_relative(refined, &fqn)
            }
            None => Type::Mixed,
        }
    }

    /// Type of `$base->prop`.
    fn prop_type(&self, base: &Expr, nullsafe: bool, name: &MemberName) -> Type {
        let base_ty = self.infer(base);
        let Some(prop) = self.member_ident(name) else { return Type::Mixed };
        let Some(fqn) = self.type_class_fqn(&base_ty) else { return Type::Mixed };
        let ty = match self.index.find_property(&fqn, &prop) {
            Some(found) if self.native => found.member.native_ty,
            Some(found) => found.member.ty,
            None => Type::Mixed,
        };
        if nullsafe {
            ty.nullable()
        } else {
            ty
        }
    }

    /// Type of `Class::$prop`.
    fn static_prop_type(&self, class: &Expr, name: &MemberName) -> Type {
        let Some(prop) = self.member_ident(name) else { return Type::Mixed };
        let Some(fqn) = self.class_type(class).and_then(|t| self.type_class_fqn(&t)) else {
            return Type::Mixed;
        };
        match self.index.find_property(&fqn, &prop) {
            Some(found) if self.native => found.member.native_ty,
            Some(found) => found.member.ty,
            None => Type::Mixed,
        }
    }

    /// Type of `Class::CONST` or `Class::class`.
    fn class_const_type(&self, class: &Expr, name: &MemberName) -> Type {
        let class_ty = self.class_type(class);
        if let Some(ident) = self.member_ident(name) {
            if ident.eq_ignore_ascii_case("class") {
                // `Foo::class` is a `class-string<Foo>`.
                return Type::ClassString(class_ty.map(Box::new));
            }
            if let Some(fqn) = class_ty.and_then(|t| self.type_class_fqn(&t)) {
                if let Some(found) = self.index.find_constant(&fqn, &ident) {
                    // A known int-valued constant is a literal-int type, so constant
                    // comparisons against it (`$x === Foo::BAR`) can be decided.
                    return match found.member.int_value {
                        Some(v) => Type::LiteralInt(v),
                        None => found.member.ty,
                    };
                }
            }
        }
        Type::Mixed
    }

    /// Type of `$base[$i]`: the value type of an array/iterable base, else mixed.
    fn index_type(&self, base: &Expr, index: Option<&Expr>) -> Type {
        match self.infer(base) {
            Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => kv.1.clone(),
            Type::List(v) => *v,
            Type::String => Type::String, // string offset is a 1-char string
            Type::Shape { fields, sealed } => {
                // A constant offset reads that field's type; otherwise the union of
                // all field types (any of them could be selected).
                match index.and_then(const_key) {
                    Some(k) => fields
                        .iter()
                        .find(|f| f.key.as_deref() == Some(k.as_str()))
                        .map(|f| f.ty.clone())
                        .unwrap_or(Type::Mixed),
                    None => {
                        let mut vals: Vec<Type> = fields.into_iter().map(|f| f.ty).collect();
                        if !sealed {
                            vals.push(Type::Mixed);
                        }
                        Type::union(vals)
                    }
                }
            }
            _ => Type::Mixed,
        }
    }

    fn unary_type(&self, op: UnOp, expr: &Expr) -> Type {
        match op {
            UnOp::Not => Type::Bool,
            // `~` is bytewise on a string (→ string), bitwise on a number (→ int).
            UnOp::BitNot => match self.infer(expr) {
                Type::String | Type::LiteralString(_) => Type::String,
                Type::Float => Type::Float,
                _ => Type::Int,
            },
            // Keep literal ints through the sign — distributing over a union — so
            // `-$x` where `$x: -1|0|1` stays `-1|0|1` (e.g. `return $neg ? -$r : $r`
            // in a `@return -1|0|1` comparator), not the absorbing `int`.
            UnOp::Plus | UnOp::Minus => apply_sign(matches!(op, UnOp::Minus), self.infer(expr)),
        }
    }

    fn binary_type(&self, op: BinOp, lhs: &Expr, rhs: &Expr) -> Type {
        use BinOp::*;
        match op {
            Concat => Type::String,
            // `&` `|` `^` are *bytewise* on two strings (→ string), bitwise on
            // numbers (→ int). Shift/modulo are always int.
            BitOr | BitAnd | BitXor => {
                if is_string_ty(&self.infer(lhs)) && is_string_ty(&self.infer(rhs)) {
                    Type::String
                } else {
                    Type::Int
                }
            }
            Shl | Shr | Mod => Type::Int,
            Eq | NotEq | Identical | NotIdentical | Lt | LtEq | Gt | GtEq | BoolAnd | BoolOr
            | LogicalAnd | LogicalOr | LogicalXor => Type::Bool,
            // The spaceship operator yields exactly `-1|0|1` (phpstan models it so,
            // which is why `@return -1|0|1` comparison methods type-check).
            Spaceship => Type::union(vec![Type::LiteralInt(-1), Type::LiteralInt(0), Type::LiteralInt(1)]),
            Coalesce => Type::union(vec![strip_null(self.infer(lhs)), self.infer(rhs)]),
            Add | Sub | Mul | Div | Pow => self.arith(op, self.infer(lhs), self.infer(rhs)),
            Pipe => Type::Mixed,
        }
    }

    /// Arithmetic result typing (`+ - * / **`).
    fn arith(&self, op: BinOp, l: Type, r: Type) -> Type {
        // `array + array` merges into an array.
        if matches!(op, BinOp::Add) && is_array(&l) && is_array(&r) {
            return Type::Array(None);
        }
        // With an unknown operand we can't know the result — stay `mixed`
        // (lenient) rather than guessing `int|float`, which would false-flag an
        // `int`/`float` use of e.g. `$untyped - 1`. This also covers a *union* that
        // contains `mixed` (`int|mixed`, common when a dynamic property feeds the
        // arithmetic), which otherwise fell through to the `int|float` arm below.
        if contains_mixed(&l) || contains_mixed(&r) {
            return Type::Mixed;
        }
        // `/` and `**` may produce a float even from two ints.
        let may_float = matches!(op, BinOp::Div | BinOp::Pow);
        if is_float(&l) || is_float(&r) {
            Type::Float
        } else if is_int(&l) && is_int(&r) {
            if may_float {
                Type::union(vec![Type::Int, Type::Float])
            } else {
                Type::Int
            }
        } else {
            Type::union(vec![Type::Int, Type::Float])
        }
    }

    // --- name / class helpers ------------------------------------------------

    /// Resolve an expression in *class-name position* (`new`, `::`, `instanceof`)
    /// to a type. Handles bare names, `self`/`static`/`parent`, and a variable
    /// holding an object/class-string.
    fn class_type(&self, e: &Expr) -> Option<Type> {
        match &e.kind {
            ExprKind::Name(n) => Some(match self.scope.resolve_class(n) {
                Resolution::Fqn(fqn) => Type::Named { fqn, args: vec![] },
                Resolution::LateStatic(s) => match s.as_str() {
                    "self" => self.self_type()?,
                    "static" => Type::StaticType,
                    _ => self.parent_type()?,
                },
                Resolution::BuiltinType(_) | Resolution::Fallback { .. } => return None,
            }),
            // `new $class` / `$obj::method()` — fall back to the value's type. A
            // `class-string<C>` operand yields an *instance* of `C` (`new $cs` is a
            // `C`, not the class-string); other strings yield a bare object.
            _ => Some(instance_of(self.infer(e))),
        }
    }

    fn self_type(&self) -> Option<Type> {
        self.class.clone().map(|fqn| Type::Named { fqn, args: vec![] })
    }

    fn parent_type(&self) -> Option<Type> {
        let cur = self.class.as_deref()?;
        self.index.class(cur)?.parents.first().cloned()
    }

    /// Late-static-bind `self`/`static`/`parent` in a member's type to the class
    /// the access was made on (`bound`). A method declared `: self` on `Factory`
    /// returns `Factory`. Recurses through composite types.
    fn bind_relative(&self, ty: Type, bound: &str) -> Type {
        match ty {
            Type::SelfType | Type::StaticType => Type::Named { fqn: bound.to_string(), args: vec![] },
            Type::Parent => self
                .index
                .class(bound)
                .and_then(|c| c.parents.first().cloned())
                .unwrap_or(Type::Parent),
            Type::Nullable(inner) => self.bind_relative(*inner, bound).nullable(),
            Type::Union(parts) => Type::union(parts.into_iter().map(|p| self.bind_relative(p, bound)).collect()),
            Type::Intersection(parts) => {
                Type::intersection(parts.into_iter().map(|p| self.bind_relative(p, bound)).collect())
            }
            Type::Array(Some(kv)) => {
                Type::Array(Some(Box::new((self.bind_relative(kv.0, bound), self.bind_relative(kv.1, bound)))))
            }
            Type::List(inner) => Type::List(Box::new(self.bind_relative(*inner, bound))),
            Type::Named { fqn, args } => {
                Type::Named { fqn, args: args.into_iter().map(|a| self.bind_relative(a, bound)).collect() }
            }
            other => other,
        }
    }

    /// The class FQN to query members on, given a value's type.
    fn type_class_fqn(&self, t: &Type) -> Option<String> {
        match t {
            Type::Named { fqn, .. } => Some(fqn.clone()),
            Type::SelfType | Type::StaticType => self.class.clone(),
            Type::Parent => self.parent_type().and_then(|p| self.type_class_fqn(&p)),
            Type::Nullable(inner) => self.type_class_fqn(inner),
            _ => None,
        }
    }

    /// The static text of a member name, or `None` for a computed/variable member.
    fn member_ident(&self, m: &MemberName) -> Option<String> {
        match m {
            MemberName::Ident(sym) => Some(self.interner.resolve(*sym).to_string()),
            MemberName::Var(_) | MemberName::Expr(_) => None,
        }
    }

    /// Look up a function's reflection from a name reference, honouring the
    /// namespaced-then-global fallback for unqualified calls.
    fn function_reflection(&self, n: &Name) -> Option<&php_reflect::FunctionReflection> {
        match self.scope.resolve_function(n) {
            Resolution::Fqn(fqn) => self.index.function(&fqn),
            Resolution::Fallback { namespaced, global } => {
                self.index.function(&namespaced).or_else(|| self.index.function(&global))
            }
            Resolution::LateStatic(_) | Resolution::BuiltinType(_) => None,
        }
    }
}

/// Map a cast to its result type.
fn cast_type(kind: CastKind) -> Type {
    match kind {
        CastKind::Int => Type::Int,
        CastKind::Float => Type::Float,
        CastKind::String => Type::String,
        CastKind::Bool => Type::Bool,
        CastKind::Array => Type::Array(None),
        CastKind::Object => Type::Object,
        CastKind::Unset => Type::Null,
        CastKind::Void => Type::Void,
    }
}

/// The type of a magic constant (`__LINE__`, `__FILE__`, …), if `name` is one.
fn magic_constant(name: &str) -> Option<Type> {
    match name {
        "__LINE__" => Some(Type::Int),
        "__FILE__" | "__DIR__" | "__FUNCTION__" | "__CLASS__" | "__TRAIT__" | "__METHOD__"
        | "__NAMESPACE__" | "__PROPERTY__" => Some(Type::String),
        _ => None,
    }
}

/// Drop `null` from a type (for `??` / nullsafe narrowing).
fn strip_null(t: Type) -> Type {
    match t {
        Type::Null => Type::Never,
        Type::Nullable(inner) => *inner,
        Type::Union(parts) => Type::union(parts.into_iter().filter(|p| *p != Type::Null).collect()),
        other => other,
    }
}

/// Drop the always-falsy members (`null`, `false`) from a type — the value the
/// truthy branch of `a ?: b` (short ternary) yields when `a` is taken.
fn strip_falsy(t: Type) -> Type {
    match t {
        Type::Null | Type::False => Type::Never,
        Type::Bool => Type::True,
        Type::Nullable(inner) => strip_falsy(*inner),
        Type::Union(parts) => {
            Type::union(parts.into_iter().filter(|p| !matches!(p, Type::Null | Type::False)).map(strip_falsy).collect())
        }
        other => other,
    }
}

/// `+$x` / `-$x`: numeric, preserving int vs float when known.
/// Apply a unary `+`/`-` to a type, preserving literal ints (negating them when
/// `neg`) and distributing over a union; non-literal operands fall back to
/// [`numeric_unary`].
fn apply_sign(neg: bool, t: Type) -> Type {
    match t {
        Type::LiteralInt(n) => Type::LiteralInt(if neg { n.wrapping_neg() } else { n }),
        Type::Union(parts) => Type::union(parts.into_iter().map(|p| apply_sign(neg, p)).collect()),
        other => numeric_unary(other),
    }
}

fn numeric_unary(t: Type) -> Type {
    if contains_mixed(&t) {
        Type::Mixed // unknown operand → don't guess `int|float` (would false-flag)
    } else if is_float(&t) {
        Type::Float
    } else if is_int(&t) {
        Type::Int
    } else {
        Type::union(vec![Type::Int, Type::Float])
    }
}

/// `++`/`--`: keeps the operand's numeric/string type, else int.
fn inc_dec_type(t: Type) -> Type {
    if is_int(&t) || is_float(&t) || matches!(t, Type::String) {
        t
    } else {
        Type::union(vec![Type::Int, Type::Float])
    }
}

/// The *instance* type produced by `new <expr>` from the expression's value type:
/// a `class-string<C>` constructs a `C`; a `class-string`/plain string constructs a
/// bare `object`; a union maps member-wise; anything else is returned unchanged.
fn instance_of(t: Type) -> Type {
    match t {
        Type::ClassString(Some(inner)) => *inner,
        Type::ClassString(None) | Type::String | Type::LiteralString(_) => Type::Object,
        Type::Union(parts) => Type::union(parts.into_iter().map(instance_of).collect()),
        other => other,
    }
}

/// The constant array-key spelled by an expression, if it is a literal string or
/// integer (`'foo'` → `foo`, `5` → `5`). Used for array-shape keys and constant
/// shape-offset reads. Non-literal keys yield `None`.
fn const_key(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Str(bytes) => Some(String::from_utf8_lossy(bytes).into_owned()),
        ExprKind::Int(n) => Some(n.to_string()),
        ExprKind::Paren(inner) => const_key(inner),
        _ => None,
    }
}

/// Static verdict for "is this type `null`?": `Some(true)` if it is exactly null,
/// `Some(false)` if it cannot be null, `None` if it might be (union with null,
/// `mixed`). Drives `=== null` / `is_null` dead-branch pruning.
fn null_truth(t: &Type) -> Option<bool> {
    match t {
        Type::Null => Some(true),
        Type::Nullable(_) | Type::Mixed | Type::Unknown(_) => None,
        Type::Union(parts) if parts.contains(&Type::Null) => None,
        _ => Some(false),
    }
}

/// The type of a string literal: a [`Type::LiteralString`] when the bytes are
/// valid UTF-8 and short enough to be worth tracking (literal-union params, value
/// comparisons), otherwise a plain `string`. Capped to avoid carrying huge
/// generated string constants around as types.
fn literal_string(bytes: &[u8]) -> Type {
    const MAX: usize = 64;
    if bytes.len() <= MAX {
        if let Ok(s) = std::str::from_utf8(bytes) {
            return Type::LiteralString(s.to_string());
        }
    }
    Type::String
}

/// Whether `e` is the `null` literal (through parentheses).
fn is_null_literal(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Name(n) => n.text.eq_ignore_ascii_case("null"),
        ExprKind::Paren(inner) => is_null_literal(inner),
        _ => false,
    }
}

/// Whether `t` is, or contains (within a union/nullable), `mixed`/`unknown`.
fn contains_mixed(t: &Type) -> bool {
    match t {
        Type::Mixed | Type::Unknown(_) => true,
        Type::Union(parts) => parts.iter().any(contains_mixed),
        Type::Nullable(inner) => contains_mixed(inner),
        _ => false,
    }
}

fn is_string_ty(t: &Type) -> bool {
    matches!(t, Type::String | Type::LiteralString(_))
}

fn is_int(t: &Type) -> bool {
    match t {
        Type::Int | Type::LiteralInt(_) => true,
        // A union of only int-like members (`0|1`, common from `$x = 0; … $x = 1;`)
        // is int-like — so arithmetic on it stays `int`, not `int|float`.
        Type::Union(parts) => parts.iter().all(is_int),
        _ => false,
    }
}
fn is_float(t: &Type) -> bool {
    match t {
        Type::Float => true,
        Type::Union(parts) => parts.iter().all(is_float),
        _ => false,
    }
}
fn is_array(t: &Type) -> bool {
    matches!(t, Type::Array(_) | Type::List(_) | Type::Shape { .. })
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_ast::{Program, StmtKind};

    /// Parse `<?php` + `src`, index it, and return (index, interner, program).
    fn build(src: &str) -> (ReflectionIndex, Interner, Program) {
        let full = format!("<?php {src}");
        let r = php_parser::parse(&full);
        assert!(!r.has_errors(), "parse errors in: {src}");
        let mut index = ReflectionIndex::new();
        index.add_file(&r.program, &r.interner);
        (index, r.interner, r.program)
    }

    /// Infer the type of the *last* top-level expression statement in `src`,
    /// with optional pre-seeded variables.
    fn infer_with(src: &str, vars: &[(&str, Type)], class: Option<&str>) -> String {
        let (index, interner, program) = build(src);
        let scope = Scope::global();
        let mut ctx = TypeCtx::new(&index, &scope, &interner);
        ctx.class = class.map(|c| c.to_string());
        for (k, v) in vars {
            ctx.vars.insert(k.to_string(), v.clone());
        }
        let expr = last_expr(&program).expect("a trailing expression statement");
        ctx.infer(expr).to_string()
    }

    fn infer(src: &str) -> String {
        infer_with(src, &[], None)
    }

    /// `array{a: int, b: string}` — a test shape.
    fn shape() -> Type {
        Type::Shape {
            fields: vec![
                php_types::ShapeField { key: Some("a".into()), optional: false, ty: Type::Int },
                php_types::ShapeField { key: Some("b".into()), optional: false, ty: Type::String },
            ],
            sealed: true,
        }
    }

    fn last_expr(p: &Program) -> Option<&Expr> {
        p.stmts.iter().rev().find_map(|s| match &s.kind {
            StmtKind::Expr(e) => Some(e),
            _ => None,
        })
    }

    #[test]
    fn literals() {
        assert_eq!(infer("42;"), "42"); // literal-int type
        assert_eq!(infer("1.5;"), "float");
        assert_eq!(infer("'hi';"), "'hi'"); // literal-string type
        assert_eq!(infer("\"a$b\";"), "string"); // interpolation widens
        assert_eq!(infer("true;"), "true");
        assert_eq!(infer("false;"), "false");
        assert_eq!(infer("null;"), "null");
        assert_eq!(infer("__LINE__;"), "int");
        assert_eq!(infer("__FILE__;"), "string");
    }

    #[test]
    fn arrays() {
        assert_eq!(infer("[];"), "array");
        // Keyless literals are lists; elements carry literal types (matching phpstan).
        assert_eq!(infer("[1, 2, 3];"), "list<1|2|3>");
        // Constant-keyed literals are array shapes.
        assert_eq!(infer("['a' => 1, 'b' => 2];"), "array{a: 1, b: 2}");
        assert_eq!(infer("[1, 'x'];"), "list<1|'x'>");
        // A dynamic key drops shape precision back to `array<K, V>`.
        assert_eq!(infer_with("[$k => 1, 'b' => 2];", &[("k", Type::String)], None), "array<string, 1|2>");
    }

    #[test]
    fn interprocedural_return_drops_null_when_guard_unreachable() {
        // A `?Name`-returning helper that returns null only when *both* args are
        // null. Called with non-null args, the guarded `return null` is pruned, so
        // the call's type is `Name`, not `?Name`.
        let src = "class Name {
            public static function concat(?Name $a, ?Name $b): ?Name {
                if ($a === null && $b === null) { return null; }
                return new Name();
            }
        }
        Name::concat($x, $y);";
        let named = Type::Named { fqn: "Name".into(), args: vec![] };
        assert_eq!(infer_with(src, &[("x", named.clone()), ("y", named)], None), "Name");
    }

    #[test]
    fn interprocedural_return_keeps_null_when_guard_reachable() {
        // Called with possibly-null args, the null path is live → stays nullable.
        let src = "class Name {
            public static function concat(?Name $a, ?Name $b): ?Name {
                if ($a === null && $b === null) { return null; }
                return new Name();
            }
        }
        Name::concat($x, $y);";
        let nn = Type::Nullable(Box::new(Type::Named { fqn: "Name".into(), args: vec![] }));
        let got = infer_with(src, &[("x", nn.clone()), ("y", nn)], None);
        assert!(got.contains("null"), "expected nullable, got {got}");
    }

    #[test]
    fn interprocedural_return_prunes_on_int_constant_guard() {
        // A `?Name` helper that returns null only when `$type !== TYPE_NORMAL`.
        // Called with `$type = TYPE_NORMAL`, that guard is statically false → the
        // null path is pruned → the call's type is `Name`.
        let src = "class C {
            const TYPE_NORMAL = 1;
            const TYPE_FUNCTION = 2;
            public function resolve(Name $name, int $type): ?Name {
                if ($type !== C::TYPE_NORMAL) { return null; }
                return $name;
            }
            public function resolveClass(Name $name): ?Name {
                return $this->resolve($name, C::TYPE_NORMAL);
            }
        }
        class Name {}
        $c->resolve($n, C::TYPE_NORMAL);";
        let vars = &[
            ("c", Type::Named { fqn: "C".into(), args: vec![] }),
            ("n", Type::Named { fqn: "Name".into(), args: vec![] }),
        ];
        assert_eq!(infer_with(src, vars, None), "Name");
    }

    #[test]
    fn short_ternary_strips_falsy() {
        // `$x ?: 5` where `$x: ?int` yields `int` (falsy `null` stripped), not `?int`.
        assert_eq!(infer_with("$x ?: 5;", &[("x", Type::Nullable(Box::new(Type::Int)))], None), "int");
    }

    #[test]
    fn shape_field_read() {
        // Reading a constant offset of a shape yields that field's type.
        assert_eq!(infer_with("$a['b'];", &[("a", shape())], None), "string");
        assert_eq!(infer_with("$a['z'];", &[("a", shape())], None), "mixed");
    }

    #[test]
    fn arithmetic() {
        assert_eq!(infer("1 + 2;"), "int");
        assert_eq!(infer("1 + 2.0;"), "float");
        assert_eq!(infer("1 / 2;"), "int|float");
        assert_eq!(infer("2 ** 3;"), "int|float");
        assert_eq!(infer("7 % 3;"), "int");
        assert_eq!(infer("'a' . 'b';"), "string");
        assert_eq!(infer("[1] + [2];"), "array");
        assert_eq!(infer("1 <=> 2;"), "-1|0|1");
    }

    #[test]
    fn comparisons_and_logic_are_bool() {
        assert_eq!(infer("1 < 2;"), "bool");
        assert_eq!(infer("1 === 1;"), "bool");
        assert_eq!(infer("true && false;"), "bool");
        assert_eq!(infer("!$x;"), "bool");
        assert_eq!(infer("$x instanceof Foo;"), "bool");
    }

    #[test]
    fn casts() {
        assert_eq!(infer("(int) $x;"), "int");
        assert_eq!(infer("(string) $x;"), "string");
        assert_eq!(infer("(array) $x;"), "array");
        assert_eq!(infer("(bool) $x;"), "bool");
    }

    #[test]
    fn ternary_and_coalesce() {
        assert_eq!(infer("true ? 1 : 'x';"), "1|'x'");
        assert_eq!(infer_with("$x ?? 0;", &[("x", Type::Nullable(Box::new(Type::String)))], None), "string|0");
    }

    #[test]
    fn variables_from_env() {
        assert_eq!(infer_with("$x;", &[("x", Type::String)], None), "string");
        assert_eq!(infer("$undefined;"), "mixed");
    }

    #[test]
    fn this_in_class_context() {
        assert_eq!(infer_with("$this;", &[], Some("App\\User")), "App\\User");
        assert_eq!(infer("$this;"), "mixed"); // no class context
    }

    #[test]
    fn new_yields_the_class() {
        let s = "namespace App; class User {} new User();";
        // Indexing happens on the whole program; the trailing `new` is the expr.
        let (index, interner, program) = build(s);
        let scope = Scope::in_namespace("App");
        let ctx = TypeCtx::new(&index, &scope, &interner);
        let expr = last_expr(&program).unwrap();
        assert_eq!(ctx.infer(expr).to_string(), "App\\User");
    }

    #[test]
    fn function_return_type() {
        let src = "function makeName(): string { return 'x'; } makeName();";
        assert_eq!(infer(src), "string");
        let src2 = "function nope() {} nope();";
        assert_eq!(infer(src2), "mixed"); // no return type -> mixed
    }

    #[test]
    fn method_and_property_types() {
        let src = r#"
            class User {
                public int $age = 0;
                public function name(): string { return ''; }
            }
        "#;
        // `$u->name()` and `$u->age` with $u : User.
        assert_eq!(
            infer_with(&format!("{src} $u->name();"), &[("u", Type::Named { fqn: "User".into(), args: vec![] })], None),
            "string"
        );
        assert_eq!(
            infer_with(&format!("{src} $u->age;"), &[("u", Type::Named { fqn: "User".into(), args: vec![] })], None),
            "int"
        );
    }

    #[test]
    fn nullsafe_method_is_nullable() {
        let src = "class A { public function f(): int { return 1; } }";
        assert_eq!(
            infer_with(&format!("{src} $a?->f();"), &[("a", Type::Named { fqn: "A".into(), args: vec![] })], None),
            "?int"
        );
    }

    #[test]
    fn static_call_and_class_const() {
        let src = r#"
            class Factory {
                const VERSION = 1;
                public static function make(): self { return new self(); }
            }
        "#;
        assert_eq!(infer(&format!("{src} Factory::make();")), "Factory");
        assert_eq!(infer(&format!("{src} Factory::class;")), "class-string<Factory>");
    }

    #[test]
    fn inherited_method_via_index() {
        let src = r#"
            class Base { public function id(): int { return 1; } }
            class User extends Base {}
        "#;
        assert_eq!(
            infer_with(&format!("{src} $u->id();"), &[("u", Type::Named { fqn: "User".into(), args: vec![] })], None),
            "int"
        );
    }

    #[test]
    fn index_into_typed_array() {
        let arr = Type::Array(Some(Box::new((Type::Int, Type::String))));
        assert_eq!(infer_with("$a[0];", &[("a", arr)], None), "string");
        assert_eq!(infer_with("$s[0];", &[("s", Type::String)], None), "string");
    }

    #[test]
    fn closure_and_match() {
        assert_eq!(infer("fn() => 1;"), "Closure");
        assert_eq!(infer("function() {};"), "Closure");
        assert_eq!(infer("match($x) { 1 => 'a', default => 2 };"), "'a'|2");
    }
}
