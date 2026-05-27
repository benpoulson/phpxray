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

pub mod arrays;
mod assign;
mod const_eval;
mod definedness;
mod flow;
pub mod refine;
mod returns;
mod type_map;

pub use assign::{
    assignable_certain, assignable_trinary, is_assignable, is_castable_to_string, native_shape,
    Trinary,
};
pub use const_eval::{eval_const, ConstVal};
pub use definedness::{undefined_variables, UndefVar};
pub use refine::{strip_false, strip_falsy, strip_null_lenient, strip_null_strict};
pub use type_map::{native_type_map, type_map, TypeMap};

use php_ast::{
    Arg, ArrowFn, BinOp, CastKind, ClosureExpr, Expr, ExprKind, MemberName, Name, Param, UnOp,
};
use php_intern::Interner;
use php_reflect::ReflectionIndex;
use php_resolve::{Resolution, Scope};
use php_types::{CallableSig, Type};
use std::collections::HashMap;

type CallableAliases = HashMap<String, CallableAlias>;

#[derive(Clone)]
pub(crate) enum CallableAlias {
    Closure {
        id: (u32, u32),
        expr: Box<ClosureExpr>,
        vars: HashMap<String, Type>,
        callables: CallableAliases,
        class: Option<String>,
    },
    Arrow {
        id: (u32, u32),
        expr: Box<ArrowFn>,
        vars: HashMap<String, Type>,
        callables: CallableAliases,
        class: Option<String>,
    },
}

impl CallableAlias {
    fn id(&self) -> (u32, u32) {
        match self {
            CallableAlias::Closure { id, .. } | CallableAlias::Arrow { id, .. } => *id,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CollectionMethod {
    Map,
    Filter,
    Each,
    Walk,
    Reduce,
}

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
    /// Flow-local callable aliases, keyed by variable name. This is private to
    /// inference and keeps closure/arrow bodies available after `$cb = fn...`.
    pub(crate) callables: CallableAliases,
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
        TypeCtx {
            index,
            scope,
            interner,
            class: None,
            vars: HashMap::new(),
            callables: HashMap::new(),
            depth: 0,
            native: false,
        }
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
            ExprKind::MethodCall {
                recv,
                nullsafe,
                method,
                args,
                ..
            } => {
                if let Some(t) = self.place_key(e).and_then(|k| self.vars.get(&k).cloned()) {
                    return t;
                }
                self.method_type(recv, *nullsafe, method, args)
            }
            ExprKind::StaticCall {
                class,
                method,
                args,
            } => self.static_call_type(class, method, args),
            ExprKind::New { class, .. } => self.class_type(class).unwrap_or(Type::Object),
            ExprKind::NewAnon { .. } => Type::Object,
            ExprKind::Prop {
                base,
                nullsafe,
                name,
            } => {
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
                    None => strip_falsy(&self.infer(cond)),
                };
                Type::union(vec![then_ty, self.infer(els)])
            }
            ExprKind::Coalesce { lhs, rhs } => {
                Type::union(vec![strip_null_strict(&self.infer(lhs)), self.infer(rhs)])
            }
            ExprKind::PreInc(e)
            | ExprKind::PreDec(e)
            | ExprKind::PostInc(e)
            | ExprKind::PostDec(e) => inc_dec_type(self.infer(e)),
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
            ExprKind::Closure(_) | ExprKind::ArrowFn(_) => Type::Named {
                fqn: "Closure".into(),
                args: vec![],
            },
            ExprKind::Throw(_) | ExprKind::Exit(_) => Type::Never,
            ExprKind::Yield { .. } | ExprKind::YieldFrom(_) => Type::Mixed,
            ExprKind::Include { .. } | ExprKind::Eval(_) => Type::Mixed,
            ExprKind::Error => Type::Mixed,
        }
    }

    /// The type of variable `$name`.
    fn variable(&self, name: &str) -> Type {
        if name == "this" {
            return self
                .class
                .clone()
                .map(|fqn| Type::Named { fqn, args: vec![] })
                .unwrap_or(Type::Mixed);
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
                return Type::Shape {
                    fields,
                    sealed: true,
                };
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
            vals.push(
                it.value
                    .as_ref()
                    .map(|v| self.infer(v))
                    .unwrap_or(Type::Mixed),
            );
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
            let key = arrays::const_shape_key(it.key.as_ref()?)?;
            if fields
                .iter()
                .any(|f| f.key.as_deref() == Some(key.as_str()))
            {
                return None; // duplicate key — not a well-formed shape
            }
            let ty = it
                .value
                .as_ref()
                .map(|v| self.infer(v))
                .unwrap_or(Type::Mixed);
            fields.push(php_types::ShapeField {
                key: Some(key),
                optional: false,
                ty,
            });
        }
        Some(fields)
    }

    /// Return type of a free function call `f(...)`.
    fn call_type(&self, callee: &Expr, args: &[php_ast::Arg]) -> Type {
        let ExprKind::Name(n) = &callee.kind else {
            return if is_first_class_callable(args) {
                Type::Callable(None)
            } else {
                Type::Mixed
            };
        };
        if is_first_class_callable(args) {
            return self
                .function_reflection(n)
                .map(|f| self.function_callable_type(f))
                .unwrap_or(Type::Callable(None));
        }
        match self.function_reflection(n) {
            Some(f) if self.native => f.native_return.clone(),
            Some(f) if f.builtin => {
                let fname = last_segment(&f.fqn).to_ascii_lowercase();
                self.dynamic_return(&fname, args)
                    .unwrap_or_else(|| f.return_type.clone())
            }
            Some(f) => {
                let declared = self.bound_call_return(&f.params, &f.return_type, args);
                let params: Vec<String> = f.params.iter().map(|p| p.name.clone()).collect();
                let body = self.index.function_body(&f.fqn);
                self.refine_return(&declared, body, &params, args, None)
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
        returns::refine_return(self, declared, body, params, args, callee_class)
    }

    /// Argument-dependent return types for selected built-ins. Returns `None` to
    /// fall back to the stub signature.
    fn dynamic_return(&self, fname: &str, args: &[php_ast::Arg]) -> Option<Type> {
        if !args_are_plain_positional(args) {
            return None;
        }

        // The string-replace family returns the *subject*'s shape: a string
        // subject yields a string, an array subject an array. The stub can only
        // say `string|array`, which then poisons every downstream string use.
        if let Some(idx) = match fname {
            "str_replace"
            | "str_ireplace"
            | "preg_replace"
            | "preg_replace_callback"
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
            "array_map" => self.array_map_return(args),
            "array_keys" => Some(Type::List(Box::new(self.array_key_type(args.first()?)?))),
            // `array_values(array<K,V>)` → `list<V>`.
            "array_values" => Some(Type::List(Box::new(self.array_value_type(args.first()?)?))),
            "array_column" => self.array_column_return(args),
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

    fn array_map_return(&self, args: &[Arg]) -> Option<Type> {
        if self.native {
            return None;
        }
        let callback = args.first()?;
        let inferred_params: Vec<Type> = args
            .iter()
            .skip(1)
            .map(|a| self.array_value_type(a).unwrap_or(Type::Mixed))
            .collect();
        if inferred_params.is_empty() {
            return None;
        }
        let ret = self.callback_return_type(callback, &inferred_params)?;
        (!template_observation_is_imprecise(&ret)).then(|| Type::List(Box::new(ret)))
    }

    fn array_column_return(&self, args: &[Arg]) -> Option<Type> {
        let rows = arrays::array_value_type(&self.infer(&args.first()?.value))?;
        let value_key = const_shape_key_arg(args.get(1)?)?;
        let value = shape_present_type(&rows, &value_key)?;
        match args.get(2) {
            None => Some(Type::List(Box::new(value))),
            Some(arg) => match nullable_const_shape_key_arg(arg)? {
                None => Some(Type::List(Box::new(value))),
                Some(index_key) => {
                    let key = shape_present_type(&rows, &index_key)?;
                    Some(Type::Array(Some(Box::new((key, value)))))
                }
            },
        }
    }

    fn collection_method_return(
        &self,
        recv_ty: &Type,
        name: &str,
        args: &[Arg],
        fallback: &Type,
    ) -> Option<Type> {
        if self.native || !args_are_plain_positional(args) {
            return None;
        }
        let method = collection_method(name)?;
        let params = self.collection_callback_params(recv_ty, method, args)?;
        let receiver = self.collection_receiver_type(recv_ty)?;
        match method {
            CollectionMethod::Map => {
                let callback = args.first()?;
                let ret = self.callback_return_type(callback, &params)?;
                if template_observation_is_imprecise(&ret) {
                    return None;
                }
                let mapped = self.collection_receiver_type_with_value(recv_ty, ret)?;
                self.collection_same_receiver_override(fallback, recv_ty, &mapped)
                    .then_some(mapped)
            }
            CollectionMethod::Filter => self
                .collection_same_receiver_override(fallback, recv_ty, &receiver)
                .then_some(receiver),
            CollectionMethod::Each | CollectionMethod::Walk => {
                collection_fallback_is_imprecise(fallback)
                    .then_some(receiver)
                    .filter(|r| self.collection_same_receiver_override(fallback, recv_ty, r))
            }
            CollectionMethod::Reduce => {
                let callback = args.first()?;
                let ret = self.callback_return_type(callback, &params)?;
                if template_observation_is_imprecise(&ret) {
                    return None;
                }
                (collection_fallback_is_imprecise(fallback)
                    || is_assignable(self.index, &ret, fallback))
                .then_some(ret)
            }
        }
    }

    fn collection_callback_params(
        &self,
        recv_ty: &Type,
        method: CollectionMethod,
        args: &[Arg],
    ) -> Option<Vec<Type>> {
        if self.native || !args_are_plain_positional(args) {
            return None;
        }
        let (key, value) = self.collection_key_value(recv_ty)?;
        match method {
            CollectionMethod::Map
            | CollectionMethod::Filter
            | CollectionMethod::Each
            | CollectionMethod::Walk => Some(vec![value, key]),
            CollectionMethod::Reduce => {
                let carry = args
                    .get(1)
                    .map(|arg| self.infer(&arg.value))
                    .unwrap_or(Type::Mixed);
                Some(vec![carry, value, key])
            }
        }
    }

    fn collection_key_value(&self, recv_ty: &Type) -> Option<(Type, Type)> {
        let (fqn, args) = receiver_named_parts(recv_ty)?;
        self.index.class(fqn)?;
        match args.len() {
            1 => {
                let value = args[0].clone();
                (!template_observation_is_imprecise(&value)).then_some((Type::Mixed, value))
            }
            n if n >= 2 => {
                let key = args[0].clone();
                let value = args[1].clone();
                (!template_observation_is_imprecise(&key)
                    && !template_observation_is_imprecise(&value))
                .then_some((key, value))
            }
            _ => None,
        }
    }

    fn collection_receiver_type(&self, recv_ty: &Type) -> Option<Type> {
        let (fqn, args) = receiver_named_parts(recv_ty)?;
        self.index.class(fqn)?;
        (!args.is_empty()).then(|| Type::Named {
            fqn: fqn.to_string(),
            args: args.to_vec(),
        })
    }

    fn collection_receiver_type_with_value(&self, recv_ty: &Type, value: Type) -> Option<Type> {
        let (fqn, args) = receiver_named_parts(recv_ty)?;
        self.index.class(fqn)?;
        let replace_at = match args.len() {
            1 => 0,
            n if n >= 2 => 1,
            _ => return None,
        };
        let mut args = args.to_vec();
        args[replace_at] = value;
        Some(Type::Named {
            fqn: fqn.to_string(),
            args,
        })
    }

    fn collection_same_receiver_override(
        &self,
        fallback: &Type,
        recv_ty: &Type,
        replacement: &Type,
    ) -> bool {
        if collection_fallback_is_imprecise(fallback) {
            return true;
        }
        let Some((fallback_fqn, _)) = receiver_named_parts(fallback) else {
            return false;
        };
        let Some((recv_fqn, _)) = receiver_named_parts(recv_ty) else {
            return false;
        };
        let Some((replacement_fqn, _)) = receiver_named_parts(replacement) else {
            return false;
        };
        fallback_fqn.eq_ignore_ascii_case(recv_fqn)
            && replacement_fqn.eq_ignore_ascii_case(recv_fqn)
    }

    /// The value (element) type of an array/list argument, if known.
    fn array_value_type(&self, arg: &php_ast::Arg) -> Option<Type> {
        arrays::array_value_type(&self.infer(&arg.value))
    }

    /// The key type of an array/list/shape argument, if known (`list` → `int`).
    fn array_key_type(&self, arg: &php_ast::Arg) -> Option<Type> {
        arrays::array_key_type(&self.infer(&arg.value))
    }

    fn bound_call_return(
        &self,
        params: &[php_reflect::ParamReflection],
        declared: &Type,
        args: &[Arg],
    ) -> Type {
        let Some(subst) = self.bind_call_templates(params, args) else {
            return declared.clone();
        };
        subst_templates(declared, &subst, true)
    }

    fn bind_call_templates(
        &self,
        params: &[php_reflect::ParamReflection],
        args: &[Arg],
    ) -> Option<HashMap<String, Type>> {
        if !args_are_plain_positional(args) {
            return None;
        }
        let mut raw = HashMap::<String, Vec<Type>>::new();
        let mut ai = 0;
        for p in params {
            if p.variadic {
                while let Some(arg) = args.get(ai) {
                    bind_templates_from_types(&p.ty, &self.infer(&arg.value), &mut raw);
                    ai += 1;
                }
                break;
            }
            let Some(arg) = args.get(ai) else {
                break;
            };
            bind_templates_from_types(&p.ty, &self.infer(&arg.value), &mut raw);
            ai += 1;
        }
        Some(finalize_subst(raw))
    }

    fn callback_return_type(&self, callback: &Arg, inferred_params: &[Type]) -> Option<Type> {
        match &peel_paren(&callback.value).kind {
            ExprKind::ArrowFn(a) => {
                let child = self.arrow_child(a, inferred_params);
                let body = child.infer(&a.body);
                Some(self.prefer_precise_callback_return(body, a.return_type.as_ref()))
            }
            ExprKind::Closure(c) => {
                let mut child = self.closure_child(c, inferred_params);
                let mut returns = Vec::new();
                returns::collect_returns(&mut child, &c.body, &mut returns);
                let body = if returns.is_empty() {
                    Type::Null
                } else {
                    Type::union(returns)
                };
                Some(self.prefer_precise_callback_return(body, c.return_type.as_ref()))
            }
            ExprKind::Variable(sym) => {
                let name = self.interner.resolve(*sym);
                if let Some(alias) = self.callables.get(name) {
                    return Some(self.callable_alias_return_type(alias, inferred_params));
                }
                self.callable_expr_type(&callback.value)
                    .and_then(|t| callback_signature_return(&t, inferred_params))
            }
            _ => self
                .callable_expr_type(&callback.value)
                .and_then(|t| callback_signature_return(&t, inferred_params)),
        }
    }

    pub(crate) fn callable_expr_type(&self, e: &Expr) -> Option<Type> {
        match &peel_paren(e).kind {
            ExprKind::Closure(c) => Some(self.closure_callable_type(c)),
            ExprKind::ArrowFn(a) => Some(self.arrow_callable_type(a)),
            ExprKind::Variable(sym) => {
                let name = self.interner.resolve(*sym);
                self.vars.get(name).and_then(|t| match t {
                    Type::Callable(_) => Some(t.clone()),
                    Type::LiteralString(s) => self
                        .function_reflection_from_text(s)
                        .map(|f| self.function_callable_type(f)),
                    _ => self.invokable_callable_type(t),
                })
            }
            ExprKind::Str(bytes) => self
                .literal_str(bytes)
                .and_then(|name| self.function_reflection_from_text(&name))
                .map(|f| self.function_callable_type(f)),
            ExprKind::Array { items, .. } => self.callable_array_type(items),
            ExprKind::Call { args, .. }
            | ExprKind::MethodCall { args, .. }
            | ExprKind::StaticCall { args, .. }
                if is_first_class_callable(args) =>
            {
                match self.infer(e) {
                    t @ Type::Callable(_) => Some(t),
                    _ => None,
                }
            }
            _ => self.invokable_callable_type(&self.infer(e)),
        }
    }

    fn closure_callable_type(&self, c: &ClosureExpr) -> Type {
        let params = c
            .params
            .iter()
            .map(|p| self.ast_param_decl_type(p))
            .collect();
        let ret = if let Some(t) = &c.return_type {
            self.bind_relative_to_current(php_reflect::resolve_ast_type(self.scope, t))
        } else {
            let mut child = self.closure_child(c, &[]);
            let mut returns = Vec::new();
            returns::collect_returns(&mut child, &c.body, &mut returns);
            if returns.is_empty() {
                Type::Null
            } else {
                Type::union(returns)
            }
        };
        Type::Callable(Some(Box::new(CallableSig { params, ret })))
    }

    fn arrow_callable_type(&self, a: &ArrowFn) -> Type {
        let params = a
            .params
            .iter()
            .map(|p| self.ast_param_decl_type(p))
            .collect();
        let ret = if let Some(t) = &a.return_type {
            self.bind_relative_to_current(php_reflect::resolve_ast_type(self.scope, t))
        } else {
            self.arrow_child(a, &[]).infer(&a.body)
        };
        Type::Callable(Some(Box::new(CallableSig { params, ret })))
    }

    fn ast_param_decl_type(&self, p: &Param) -> Type {
        if self.native {
            return if p.variadic {
                Type::Array(None)
            } else {
                p.ty.as_ref()
                    .map(|t| php_reflect::resolve_ast_type(self.scope, t))
                    .unwrap_or(Type::Mixed)
            };
        }
        match &p.ty {
            Some(t) if p.variadic => {
                Type::List(Box::new(php_reflect::resolve_ast_type(self.scope, t)))
            }
            Some(t) => php_reflect::resolve_ast_type(self.scope, t),
            None if p.variadic => Type::List(Box::new(Type::Mixed)),
            None => Type::Mixed,
        }
    }

    fn callable_alias_return_type(&self, alias: &CallableAlias, inferred_params: &[Type]) -> Type {
        match alias {
            CallableAlias::Closure {
                expr,
                vars,
                callables,
                class,
                ..
            } => {
                let mut child = self.child_with_env(class.clone(), vars.clone(), callables.clone());
                child.seed_callback_params(&expr.params, inferred_params);
                let mut returns = Vec::new();
                returns::collect_returns(&mut child, &expr.body, &mut returns);
                let body = if returns.is_empty() {
                    Type::Null
                } else {
                    Type::union(returns)
                };
                self.prefer_precise_callback_return(body, expr.return_type.as_ref())
            }
            CallableAlias::Arrow {
                expr,
                vars,
                callables,
                class,
                ..
            } => {
                let mut child = self.child_with_env(class.clone(), vars.clone(), callables.clone());
                child.seed_callback_params(&expr.params, inferred_params);
                let body = child.infer(&expr.body);
                self.prefer_precise_callback_return(body, expr.return_type.as_ref())
            }
        }
    }

    fn prefer_precise_callback_return(&self, body: Type, declared: Option<&php_ast::Type>) -> Type {
        if !template_observation_is_imprecise(&body) {
            return body;
        }
        declared
            .map(|t| self.bind_relative_to_current(php_reflect::resolve_ast_type(self.scope, t)))
            .unwrap_or(body)
    }

    fn closure_child(&self, c: &ClosureExpr, inferred_params: &[Type]) -> TypeCtx<'a> {
        let mut child = TypeCtx::new(self.index, self.scope, self.interner);
        child.class = (!c.is_static).then(|| self.class.clone()).flatten();
        child.depth = self.depth;
        child.native = self.native;
        for u in &c.uses {
            let name = self.interner.resolve(u.name).to_string();
            let ty = self.vars.get(&name).cloned().unwrap_or(Type::Mixed);
            child.vars.insert(name.clone(), ty);
            if let Some(alias) = self.callables.get(&name) {
                child.callables.insert(name, alias.clone());
            }
        }
        child.seed_callback_params(&c.params, inferred_params);
        child
    }

    fn arrow_child(&self, a: &ArrowFn, inferred_params: &[Type]) -> TypeCtx<'a> {
        let mut child = TypeCtx::new(self.index, self.scope, self.interner);
        child.class = (!a.is_static).then(|| self.class.clone()).flatten();
        child.depth = self.depth;
        child.native = self.native;
        child.vars = self.vars.clone();
        child.callables = self.callables.clone();
        if a.is_static {
            strip_this_vars(&mut child.vars);
        }
        child.seed_callback_params(&a.params, inferred_params);
        child
    }

    pub(crate) fn child_with_env(
        &self,
        class: Option<String>,
        vars: HashMap<String, Type>,
        callables: CallableAliases,
    ) -> TypeCtx<'a> {
        let mut child = TypeCtx::new(self.index, self.scope, self.interner);
        child.class = class;
        child.vars = vars;
        child.callables = callables;
        child.depth = self.depth;
        child.native = self.native;
        child
    }

    fn seed_callback_params(&mut self, params: &[Param], inferred: &[Type]) {
        for (i, p) in params.iter().enumerate() {
            let name = self.interner.resolve(p.name).to_string();
            let ty = if let Some(t) = &p.ty {
                let ty = php_reflect::resolve_ast_type(self.scope, t);
                if p.variadic {
                    Type::List(Box::new(ty))
                } else {
                    ty
                }
            } else if p.variadic {
                let rest = &inferred[i.min(inferred.len())..];
                let item = if rest.is_empty() {
                    Type::Mixed
                } else {
                    Type::union(rest.to_vec())
                };
                Type::List(Box::new(item))
            } else {
                inferred.get(i).cloned().unwrap_or(Type::Mixed)
            };
            self.vars.insert(name, ty);
        }
    }

    /// Return type of `$recv->method(...)`.
    fn method_type(
        &self,
        recv: &Expr,
        nullsafe: bool,
        method: &MemberName,
        args: &[php_ast::Arg],
    ) -> Type {
        let recv_ty = self.infer(recv);
        let Some(name) = self.member_ident(method) else {
            return if is_first_class_callable(args) {
                Type::Callable(None)
            } else {
                Type::Mixed
            };
        };
        let Some(fqn) = self.type_class_fqn(&recv_ty) else {
            return if is_first_class_callable(args) {
                Type::Callable(None)
            } else {
                Type::Mixed
            };
        };
        if is_first_class_callable(args) {
            return self
                .find_method_for_receiver(&recv_ty, &fqn, &name)
                .map(|found| self.method_callable_type(&found.member, &fqn))
                .unwrap_or(Type::Callable(None));
        }
        let found = self.find_method_for_receiver(&recv_ty, &fqn, &name);
        let ret = match &found {
            Some(found) if self.native => {
                self.bind_relative(found.member.native_return.clone(), &fqn)
            }
            Some(found) => {
                let declared =
                    self.bound_call_return(&found.member.params, &found.member.return_type, args);
                let params: Vec<String> =
                    found.member.params.iter().map(|p| p.name.clone()).collect();
                let body = self.index.method_body(&found.declaring_class, &name);
                let refined = self.refine_return(&declared, body, &params, args, Some(fqn.clone()));
                self.bind_relative(refined, &fqn)
            }
            None => Type::Mixed,
        };
        let ret = if found.is_some() {
            self.collection_method_return(&recv_ty, &name, args, &ret)
                .unwrap_or(ret)
        } else {
            ret
        };
        if nullsafe {
            ret.nullable()
        } else {
            ret
        }
    }

    /// Return type of `Class::method(...)`.
    fn static_call_type(&self, class: &Expr, method: &MemberName, args: &[php_ast::Arg]) -> Type {
        let Some(name) = self.member_ident(method) else {
            return if is_first_class_callable(args) {
                Type::Callable(None)
            } else {
                Type::Mixed
            };
        };
        let Some(fqn) = self.class_type(class).and_then(|t| self.type_class_fqn(&t)) else {
            return if is_first_class_callable(args) {
                Type::Callable(None)
            } else {
                Type::Mixed
            };
        };
        if is_first_class_callable(args) {
            return self
                .index
                .find_method(&fqn, &name)
                .map(|found| self.method_callable_type(&found.member, &fqn))
                .unwrap_or(Type::Callable(None));
        }
        match self.index.find_method(&fqn, &name) {
            Some(found) if self.native => self.bind_relative(found.member.native_return, &fqn),
            Some(found) => {
                let declared =
                    self.bound_call_return(&found.member.params, &found.member.return_type, args);
                let params: Vec<String> =
                    found.member.params.iter().map(|p| p.name.clone()).collect();
                let body = self.index.method_body(&found.declaring_class, &name);
                let refined = self.refine_return(&declared, body, &params, args, Some(fqn.clone()));
                self.bind_relative(refined, &fqn)
            }
            None => Type::Mixed,
        }
    }

    /// Type of `$base->prop`.
    fn prop_type(&self, base: &Expr, nullsafe: bool, name: &MemberName) -> Type {
        let base_ty = self.infer(base);
        let Some(prop) = self.member_ident(name) else {
            return Type::Mixed;
        };
        let Some(fqn) = self.type_class_fqn(&base_ty) else {
            return Type::Mixed;
        };
        let ty = match self.find_property_for_receiver(&base_ty, &fqn, &prop) {
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
        let Some(prop) = self.member_ident(name) else {
            return Type::Mixed;
        };
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
                match index.and_then(arrays::const_shape_key) {
                    Some(k) => {
                        let shape = Type::Shape { fields, sealed };
                        match arrays::shape_offset_status(&shape, &k) {
                            Some(arrays::ShapeOffsetStatus::Present(ty)) => ty,
                            _ => Type::Mixed,
                        }
                    }
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
            Spaceship => Type::union(vec![
                Type::LiteralInt(-1),
                Type::LiteralInt(0),
                Type::LiteralInt(1),
            ]),
            Coalesce => Type::union(vec![strip_null_strict(&self.infer(lhs)), self.infer(rhs)]),
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
        self.class
            .clone()
            .map(|fqn| Type::Named { fqn, args: vec![] })
    }

    fn parent_type(&self) -> Option<Type> {
        let cur = self.class.as_deref()?;
        self.index.class(cur)?.parents.first().cloned()
    }

    /// Late-static-bind `self`/`static`/`parent` in a member's type to the class
    /// the access was made on (`bound`). A method declared `: self` on `Factory`
    /// returns `Factory`. Recurses through composite types.
    fn bind_relative(&self, ty: Type, bound: &str) -> Type {
        ty.map(&mut |part| match part {
            Type::SelfType | Type::StaticType => Type::Named {
                fqn: bound.to_string(),
                args: vec![],
            },
            Type::Parent => self
                .index
                .class(bound)
                .and_then(|c| c.parents.first().cloned())
                .unwrap_or(Type::Parent),
            other => other,
        })
    }

    fn bind_relative_to_current(&self, ty: Type) -> Type {
        match self.class.as_deref() {
            Some(class) => self.bind_relative(ty, class),
            None => ty,
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

    fn find_method_for_receiver(
        &self,
        recv_ty: &Type,
        fqn: &str,
        name: &str,
    ) -> Option<php_reflect::Found<php_reflect::MethodReflection>> {
        if self.native {
            self.index.find_method(fqn, name)
        } else {
            self.index
                .find_method_on_type(recv_ty, name)
                .or_else(|| self.index.find_method(fqn, name))
        }
    }

    fn find_property_for_receiver(
        &self,
        recv_ty: &Type,
        fqn: &str,
        name: &str,
    ) -> Option<php_reflect::Found<php_reflect::PropertyReflection>> {
        if self.native {
            self.index.find_property(fqn, name)
        } else {
            self.index
                .find_property_on_type(recv_ty, name)
                .or_else(|| self.index.find_property(fqn, name))
        }
    }

    /// Look up a function's reflection from a name reference, honouring the
    /// namespaced-then-global fallback for unqualified calls.
    fn function_reflection(&self, n: &Name) -> Option<&php_reflect::FunctionReflection> {
        match self.scope.resolve_function(n) {
            Resolution::Fqn(fqn) => self.index.function(&fqn),
            Resolution::Fallback { namespaced, global } => self
                .index
                .function(&namespaced)
                .or_else(|| self.index.function(&global)),
            Resolution::LateStatic(_) | Resolution::BuiltinType(_) => None,
        }
    }

    fn function_reflection_from_text(
        &self,
        name: &str,
    ) -> Option<&php_reflect::FunctionReflection> {
        if name.contains('\\') || name.starts_with('\\') {
            return self.index.function(name);
        }
        self.index
            .function(&self.scope.qualify(name))
            .or_else(|| self.index.function(name))
    }

    fn class_fqn_from_text(&self, name: &str) -> Option<String> {
        if name.contains('\\') || name.starts_with('\\') {
            return self.index.class(name).map(|c| c.fqn.clone());
        }
        self.index
            .class(name)
            .or_else(|| self.index.class(&self.scope.qualify(name)))
            .map(|c| c.fqn.clone())
    }

    fn callable_array_type(&self, items: &[php_ast::ArrayItem]) -> Option<Type> {
        let [target, method] = items else { return None };
        if target.spread || method.spread || target.key.is_some() || method.key.is_some() {
            return None;
        }
        let target = target.value.as_ref()?;
        let method = method.value.as_ref()?;
        let method_name = self.literal_str_expr(method)?;

        if let Some(class) = self.class_fqn_from_callable_array_target(target) {
            return self
                .index
                .find_method(&class, &method_name)
                .map(|found| self.method_callable_type(&found.member, &class));
        }

        let recv_ty = self.infer(target);
        let fqn = self.type_class_fqn(&recv_ty)?;
        self.find_method_for_receiver(&recv_ty, &fqn, &method_name)
            .map(|found| self.method_callable_type(&found.member, &fqn))
    }

    fn class_fqn_from_callable_array_target(&self, e: &Expr) -> Option<String> {
        match &peel_paren(e).kind {
            ExprKind::ClassConst { class, name } => {
                let ident = self.member_ident(name)?;
                if !ident.eq_ignore_ascii_case("class") {
                    return None;
                }
                self.class_type(class).and_then(|t| self.type_class_fqn(&t))
            }
            ExprKind::Str(bytes) => self
                .literal_str(bytes)
                .and_then(|name| self.class_fqn_from_text(&name)),
            _ => None,
        }
    }

    fn invokable_callable_type(&self, ty: &Type) -> Option<Type> {
        let fqn = self.type_class_fqn(ty)?;
        self.find_method_for_receiver(ty, &fqn, "__invoke")
            .map(|found| self.method_callable_type(&found.member, &fqn))
    }

    fn literal_str_expr(&self, e: &Expr) -> Option<String> {
        match &peel_paren(e).kind {
            ExprKind::Str(bytes) => self.literal_str(bytes),
            _ => None,
        }
    }

    fn literal_str(&self, bytes: &[u8]) -> Option<String> {
        std::str::from_utf8(bytes).ok().map(str::to_string)
    }

    fn function_callable_type(&self, f: &php_reflect::FunctionReflection) -> Type {
        let params = f
            .params
            .iter()
            .map(|p| {
                if self.native {
                    p.native_ty.clone()
                } else {
                    p.ty.clone()
                }
            })
            .collect();
        let ret = if self.native {
            f.native_return.clone()
        } else {
            f.return_type.clone()
        };
        Type::Callable(Some(Box::new(CallableSig { params, ret })))
    }

    fn method_callable_type(&self, m: &php_reflect::MethodReflection, bound: &str) -> Type {
        let params = m
            .params
            .iter()
            .map(|p| {
                let ty = if self.native {
                    p.native_ty.clone()
                } else {
                    p.ty.clone()
                };
                self.bind_relative(ty, bound)
            })
            .collect();
        let ret = if self.native {
            m.native_return.clone()
        } else {
            m.return_type.clone()
        };
        Type::Callable(Some(Box::new(CallableSig {
            params,
            ret: self.bind_relative(ret, bound),
        })))
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

fn is_first_class_callable(args: &[php_ast::Arg]) -> bool {
    args.iter().any(|a| a.placeholder)
}

fn args_are_plain_positional(args: &[Arg]) -> bool {
    args.iter()
        .all(|a| !a.spread && !a.placeholder && a.name.is_none())
}

fn peel_paren(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Paren(inner) => peel_paren(inner),
        _ => e,
    }
}

fn last_segment(name: &str) -> &str {
    name.trim_start_matches('\\')
        .rsplit('\\')
        .next()
        .unwrap_or(name)
}

fn collection_method(name: &str) -> Option<CollectionMethod> {
    match name.to_ascii_lowercase().as_str() {
        "map" => Some(CollectionMethod::Map),
        "filter" => Some(CollectionMethod::Filter),
        "each" => Some(CollectionMethod::Each),
        "walk" => Some(CollectionMethod::Walk),
        "reduce" => Some(CollectionMethod::Reduce),
        _ => None,
    }
}

fn receiver_named_parts(ty: &Type) -> Option<(&str, &[Type])> {
    match ty {
        Type::Named { fqn, args } => Some((fqn.as_str(), args.as_slice())),
        Type::Nullable(inner) => receiver_named_parts(inner),
        _ => None,
    }
}

fn collection_fallback_is_imprecise(ty: &Type) -> bool {
    template_observation_is_imprecise(ty)
}

fn const_shape_key_arg(arg: &Arg) -> Option<String> {
    arrays::const_shape_key(peel_paren(&arg.value))
}

fn nullable_const_shape_key_arg(arg: &Arg) -> Option<Option<String>> {
    if is_null_literal(peel_paren(&arg.value)) {
        Some(None)
    } else {
        const_shape_key_arg(arg).map(Some)
    }
}

fn callback_signature_return(callable: &Type, inferred_params: &[Type]) -> Option<Type> {
    let Type::Callable(Some(sig)) = callable else {
        return None;
    };
    let mut raw = HashMap::<String, Vec<Type>>::new();
    for (param, inferred) in sig.params.iter().zip(inferred_params) {
        bind_templates_from_types(param, inferred, &mut raw);
    }
    let subst = finalize_subst(raw);
    Some(subst_templates(&sig.ret, &subst, true))
}

fn shape_present_type(rows: &Type, key: &str) -> Option<Type> {
    match arrays::shape_offset_status(rows, key)? {
        arrays::ShapeOffsetStatus::Present(ty) => Some(ty),
        arrays::ShapeOffsetStatus::Missing | arrays::ShapeOffsetStatus::Maybe => None,
    }
}

fn bind_templates_from_types(param: &Type, arg: &Type, subst: &mut HashMap<String, Vec<Type>>) {
    match param {
        Type::TemplateVar(name) => {
            if !template_observation_is_imprecise(arg) {
                subst.entry(name.clone()).or_default().push(arg.clone());
            }
        }
        Type::Nullable(inner) => bind_templates_from_types(inner, arg, subst),
        Type::Union(parts) | Type::Intersection(parts) => {
            for part in parts {
                bind_templates_from_types(part, arg, subst);
            }
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            let (arg_k, arg_v) = arrays::iter_key_value(arg);
            bind_templates_from_types(&kv.0, &arg_k, subst);
            bind_templates_from_types(&kv.1, &arg_v, subst);
        }
        Type::List(inner) => {
            if let Some(v) = arrays::array_value_type(arg) {
                bind_templates_from_types(inner, &v, subst);
            }
        }
        Type::Named { fqn, args } => {
            let Type::Named {
                fqn: arg_fqn,
                args: arg_args,
            } = arg
            else {
                return;
            };
            if fqn.eq_ignore_ascii_case(arg_fqn) {
                for (p, a) in args.iter().zip(arg_args) {
                    bind_templates_from_types(p, a, subst);
                }
            }
        }
        Type::ClassString(Some(inner)) => {
            if let Type::ClassString(Some(arg_inner)) = arg {
                bind_templates_from_types(inner, arg_inner, subst);
            }
        }
        Type::Callable(Some(sig)) => {
            if let Type::Callable(Some(arg_sig)) = arg {
                for (p, a) in sig.params.iter().zip(&arg_sig.params) {
                    bind_templates_from_types(p, a, subst);
                }
                bind_templates_from_types(&sig.ret, &arg_sig.ret, subst);
            }
        }
        Type::Shape { fields, .. } => {
            if let Type::Shape {
                fields: arg_fields, ..
            } = arg
            {
                for field in fields {
                    let Some(key) = &field.key else { continue };
                    if let Some(arg_field) =
                        arg_fields.iter().find(|f| f.key.as_deref() == Some(key))
                    {
                        bind_templates_from_types(&field.ty, &arg_field.ty, subst);
                    }
                }
            }
        }
        Type::Array(None)
        | Type::Iterable(None)
        | Type::Callable(None)
        | Type::ClassString(None)
        | Type::Conditional { .. }
        | Type::Mixed
        | Type::ExplicitMixed
        | Type::Never
        | Type::Void
        | Type::Null
        | Type::Bool
        | Type::True
        | Type::False
        | Type::Int
        | Type::IntRange { .. }
        | Type::Float
        | Type::String
        | Type::Object
        | Type::Resource
        | Type::SelfType
        | Type::StaticType
        | Type::Parent
        | Type::LiteralInt(_)
        | Type::LiteralString(_)
        | Type::Unknown(_) => {}
    }
}

fn finalize_subst(raw: HashMap<String, Vec<Type>>) -> HashMap<String, Type> {
    raw.into_iter()
        .map(|(name, observations)| (name, Type::union(observations)))
        .collect()
}

fn subst_templates(ty: &Type, subst: &HashMap<String, Type>, unbound_to_mixed: bool) -> Type {
    ty.clone().map(&mut |part| match part {
        Type::TemplateVar(name) => subst.get(&name).cloned().unwrap_or({
            if unbound_to_mixed {
                Type::Mixed
            } else {
                Type::TemplateVar(name)
            }
        }),
        Type::Union(parts) => Type::union(parts),
        Type::Intersection(parts) => Type::intersection(parts),
        other => other,
    })
}

fn template_observation_is_imprecise(t: &Type) -> bool {
    let mut imprecise = false;
    let _ = t.clone().map(&mut |part| {
        if matches!(
            part,
            Type::Mixed | Type::ExplicitMixed | Type::Unknown(_) | Type::TemplateVar(_)
        ) {
            imprecise = true;
        }
        part
    });
    imprecise
}

fn strip_this_vars(vars: &mut HashMap<String, Type>) {
    vars.retain(|k, _| k != "this" && !k.starts_with("this->"));
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

/// Static verdict for "is this type `null`?": `Some(true)` if it is exactly null,
/// `Some(false)` if it cannot be null, `None` if it might be (union with null,
/// `mixed`). Drives `=== null` / `is_null` dead-branch pruning.
fn null_truth(t: &Type) -> Option<bool> {
    match t {
        Type::Null => Some(true),
        Type::Nullable(_) | Type::Mixed | Type::ExplicitMixed | Type::Unknown(_) => None,
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

/// Whether `t` is, or contains, `mixed`/`unknown`.
fn contains_mixed(t: &Type) -> bool {
    let mut found = false;
    let _ = t.clone().map(&mut |part| {
        if matches!(part, Type::Mixed | Type::ExplicitMixed | Type::Unknown(_)) {
            found = true;
        }
        part
    });
    found
}

fn is_string_ty(t: &Type) -> bool {
    matches!(t, Type::String | Type::LiteralString(_))
}

/// The `(min, max)` integer bounds of an int-valued type (`None` = unbounded),
/// or `None` if the type isn't a plain int/range/literal-int.
fn int_bounds(t: &Type) -> Option<(Option<i64>, Option<i64>)> {
    match t {
        Type::Int => Some((None, None)),
        Type::LiteralInt(n) => Some((Some(*n), Some(*n))),
        Type::IntRange { min, max } => Some((*min, *max)),
        _ => None,
    }
}

/// Statically decide `a OP b` between two integer ranges, when the ranges make it
/// certain; `None` if they overlap. `a`/`b` are `(min, max)` with `None` = ±∞.
fn cmp_ranges(
    op: BinOp,
    a: (Option<i64>, Option<i64>),
    b: (Option<i64>, Option<i64>),
) -> Option<bool> {
    let (a_lo, a_hi) = a;
    let (b_lo, b_hi) = b;
    // `a < b` is always true iff max(a) < min(b); always false iff min(a) >= max(b).
    let always_lt = matches!((a_hi, b_lo), (Some(ah), Some(bl)) if ah < bl);
    let always_ge = matches!((a_lo, b_hi), (Some(al), Some(bh)) if al >= bh);
    // `a <= b` always true iff max(a) <= min(b); always false iff min(a) > max(b).
    let always_le = matches!((a_hi, b_lo), (Some(ah), Some(bl)) if ah <= bl);
    let always_gt = matches!((a_lo, b_hi), (Some(al), Some(bh)) if al > bh);
    match op {
        BinOp::Lt if always_lt => Some(true),
        BinOp::Lt if always_ge => Some(false),
        BinOp::GtEq if always_ge => Some(true),
        BinOp::GtEq if always_lt => Some(false),
        BinOp::LtEq if always_le => Some(true),
        BinOp::LtEq if always_gt => Some(false),
        BinOp::Gt if always_gt => Some(true),
        BinOp::Gt if always_le => Some(false),
        _ => None,
    }
}

fn is_int(t: &Type) -> bool {
    match t {
        Type::Int | Type::LiteralInt(_) | Type::IntRange { .. } => true,
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
        let mut index = ReflectionIndex::with_builtins();
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
                php_types::ShapeField {
                    key: Some("a".into()),
                    optional: false,
                    ty: Type::Int,
                },
                php_types::ShapeField {
                    key: Some("b".into()),
                    optional: false,
                    ty: Type::String,
                },
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
        assert_eq!(
            infer_with("[$k => 1, 'b' => 2];", &[("k", Type::String)], None),
            "array<string, 1|2>"
        );
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
        let named = Type::Named {
            fqn: "Name".into(),
            args: vec![],
        };
        assert_eq!(
            infer_with(src, &[("x", named.clone()), ("y", named)], None),
            "Name"
        );
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
        let nn = Type::Nullable(Box::new(Type::Named {
            fqn: "Name".into(),
            args: vec![],
        }));
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
            (
                "c",
                Type::Named {
                    fqn: "C".into(),
                    args: vec![],
                },
            ),
            (
                "n",
                Type::Named {
                    fqn: "Name".into(),
                    args: vec![],
                },
            ),
        ];
        assert_eq!(infer_with(src, vars, None), "Name");
    }

    #[test]
    fn short_ternary_strips_falsy() {
        // `$x ?: 5` where `$x: ?int` yields `int` (falsy `null` stripped), not `?int`.
        assert_eq!(
            infer_with(
                "$x ?: 5;",
                &[("x", Type::Nullable(Box::new(Type::Int)))],
                None
            ),
            "int"
        );
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
        assert_eq!(
            infer_with(
                "$x ?? 0;",
                &[("x", Type::Nullable(Box::new(Type::String)))],
                None
            ),
            "string|0"
        );
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
            infer_with(
                &format!("{src} $u->name();"),
                &[(
                    "u",
                    Type::Named {
                        fqn: "User".into(),
                        args: vec![]
                    }
                )],
                None
            ),
            "string"
        );
        assert_eq!(
            infer_with(
                &format!("{src} $u->age;"),
                &[(
                    "u",
                    Type::Named {
                        fqn: "User".into(),
                        args: vec![]
                    }
                )],
                None
            ),
            "int"
        );
    }

    #[test]
    fn nullsafe_method_is_nullable() {
        let src = "class A { public function f(): int { return 1; } }";
        assert_eq!(
            infer_with(
                &format!("{src} $a?->f();"),
                &[(
                    "a",
                    Type::Named {
                        fqn: "A".into(),
                        args: vec![]
                    }
                )],
                None
            ),
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
        assert_eq!(
            infer(&format!("{src} Factory::class;")),
            "class-string<Factory>"
        );
    }

    #[test]
    fn inherited_method_via_index() {
        let src = r#"
            class Base { public function id(): int { return 1; } }
            class User extends Base {}
        "#;
        assert_eq!(
            infer_with(
                &format!("{src} $u->id();"),
                &[(
                    "u",
                    Type::Named {
                        fqn: "User".into(),
                        args: vec![]
                    }
                )],
                None
            ),
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
