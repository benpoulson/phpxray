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
mod flow;
mod type_map;

pub use assign::{is_assignable, is_castable_to_string};
pub use const_eval::{eval_const, ConstVal};
pub use type_map::{type_map, TypeMap};

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
}

impl<'a> TypeCtx<'a> {
    /// A context with no class and no known variables.
    pub fn new(index: &'a ReflectionIndex, scope: &'a Scope, interner: &'a Interner) -> Self {
        TypeCtx { index, scope, interner, class: None, vars: HashMap::new() }
    }

    /// Infer the type of `e`.
    pub fn infer(&self, e: &Expr) -> Type {
        match &e.kind {
            // --- literals ---
            ExprKind::Int(_) => Type::Int,
            ExprKind::Float(_) => Type::Float,
            ExprKind::Str(_) => Type::String,
            ExprKind::Interpolated(_) | ExprKind::ShellExec(_) => Type::String,

            // --- references ---
            ExprKind::Variable(sym) => self.variable(self.interner.resolve(*sym)),
            ExprKind::Name(n) => self.name_type(n),
            ExprKind::DollarBrace(inner) => self.infer(inner),
            ExprKind::VariableVariable(_) => Type::Mixed,

            // --- composite ---
            ExprKind::Array { items, .. } => self.array_type(items),
            ExprKind::Call { callee, .. } => self.call_type(callee),
            ExprKind::MethodCall { recv, nullsafe, method, .. } => {
                self.method_type(recv, *nullsafe, method)
            }
            ExprKind::StaticCall { class, method, .. } => self.static_call_type(class, method),
            ExprKind::New { class, .. } => self.class_type(class).unwrap_or(Type::Object),
            ExprKind::NewAnon { .. } => Type::Object,
            ExprKind::Prop { base, nullsafe, name } => self.prop_type(base, *nullsafe, name),
            ExprKind::StaticProp { class, name } => self.static_prop_type(class, name),
            ExprKind::ClassConst { class, name } => self.class_const_type(class, name),
            ExprKind::Index { base, .. } => self.index_type(base),

            // --- operators ---
            ExprKind::Unary { op, expr } => self.unary_type(*op, expr),
            ExprKind::Binary { op, lhs, rhs } => self.binary_type(*op, lhs, rhs),
            ExprKind::Assign { rhs, .. } | ExprKind::AssignRef { rhs, .. } => self.infer(rhs),
            ExprKind::AssignOp { op, target, rhs } => self.binary_type(*op, target, rhs),
            ExprKind::Cast { kind, .. } => cast_type(*kind),
            ExprKind::Ternary { then, els, cond } => {
                let then_ty = then.as_ref().map(|t| self.infer(t)).unwrap_or_else(|| self.infer(cond));
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
        if items.is_empty() || items.iter().any(|i| i.spread) {
            return Type::Array(None);
        }
        let mut keys = Vec::new();
        let mut vals = Vec::new();
        for it in items {
            match &it.key {
                Some(k) => keys.push(self.infer(k)),
                None => keys.push(Type::Int), // list-style integer key
            }
            vals.push(it.value.as_ref().map(|v| self.infer(v)).unwrap_or(Type::Mixed));
        }
        Type::Array(Some(Box::new((Type::union(keys), Type::union(vals)))))
    }

    /// Return type of a free function call `f(...)`.
    fn call_type(&self, callee: &Expr) -> Type {
        let ExprKind::Name(n) = &callee.kind else { return Type::Mixed };
        match self.function_reflection(n) {
            Some(f) => f.return_type.clone(),
            None => Type::Mixed,
        }
    }

    /// Return type of `$recv->method(...)`.
    fn method_type(&self, recv: &Expr, nullsafe: bool, method: &MemberName) -> Type {
        let recv_ty = self.infer(recv);
        let Some(name) = self.member_ident(method) else { return Type::Mixed };
        let Some(fqn) = self.type_class_fqn(&recv_ty) else { return Type::Mixed };
        let ret = match self.index.find_method(&fqn, &name) {
            Some(found) => self.bind_relative(found.member.return_type, &fqn),
            None => Type::Mixed,
        };
        if nullsafe {
            ret.nullable()
        } else {
            ret
        }
    }

    /// Return type of `Class::method(...)`.
    fn static_call_type(&self, class: &Expr, method: &MemberName) -> Type {
        let Some(name) = self.member_ident(method) else { return Type::Mixed };
        let Some(fqn) = self.class_type(class).and_then(|t| self.type_class_fqn(&t)) else {
            return Type::Mixed;
        };
        match self.index.find_method(&fqn, &name) {
            Some(found) => self.bind_relative(found.member.return_type, &fqn),
            None => Type::Mixed,
        }
    }

    /// Type of `$base->prop`.
    fn prop_type(&self, base: &Expr, nullsafe: bool, name: &MemberName) -> Type {
        let base_ty = self.infer(base);
        let Some(prop) = self.member_ident(name) else { return Type::Mixed };
        let Some(fqn) = self.type_class_fqn(&base_ty) else { return Type::Mixed };
        let ty = match self.index.find_property(&fqn, &prop) {
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
                    return found.member.ty;
                }
            }
        }
        Type::Mixed
    }

    /// Type of `$base[$i]`: the value type of an array/iterable base, else mixed.
    fn index_type(&self, base: &Expr) -> Type {
        match self.infer(base) {
            Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => kv.1.clone(),
            Type::List(v) => *v,
            Type::String => Type::String, // string offset is a 1-char string
            _ => Type::Mixed,
        }
    }

    fn unary_type(&self, op: UnOp, expr: &Expr) -> Type {
        match op {
            UnOp::Not => Type::Bool,
            UnOp::BitNot => Type::Int,
            UnOp::Plus | UnOp::Minus => numeric_unary(self.infer(expr)),
        }
    }

    fn binary_type(&self, op: BinOp, lhs: &Expr, rhs: &Expr) -> Type {
        use BinOp::*;
        match op {
            Concat => Type::String,
            BitOr | BitAnd | BitXor | Shl | Shr | Mod => Type::Int,
            Eq | NotEq | Identical | NotIdentical | Lt | LtEq | Gt | GtEq | BoolAnd | BoolOr
            | LogicalAnd | LogicalOr | LogicalXor => Type::Bool,
            Spaceship => Type::Int,
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
            // `new $class` / `$obj::method()` — fall back to the value's type.
            _ => Some(self.infer(e)),
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

/// `+$x` / `-$x`: numeric, preserving int vs float when known.
fn numeric_unary(t: Type) -> Type {
    if is_float(&t) {
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

fn is_int(t: &Type) -> bool {
    matches!(t, Type::Int | Type::LiteralInt(_))
}
fn is_float(t: &Type) -> bool {
    matches!(t, Type::Float)
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

    fn last_expr(p: &Program) -> Option<&Expr> {
        p.stmts.iter().rev().find_map(|s| match &s.kind {
            StmtKind::Expr(e) => Some(e),
            _ => None,
        })
    }

    #[test]
    fn literals() {
        assert_eq!(infer("42;"), "int");
        assert_eq!(infer("1.5;"), "float");
        assert_eq!(infer("'hi';"), "string");
        assert_eq!(infer("\"a$b\";"), "string");
        assert_eq!(infer("true;"), "true");
        assert_eq!(infer("false;"), "false");
        assert_eq!(infer("null;"), "null");
        assert_eq!(infer("__LINE__;"), "int");
        assert_eq!(infer("__FILE__;"), "string");
    }

    #[test]
    fn arrays() {
        assert_eq!(infer("[];"), "array");
        assert_eq!(infer("[1, 2, 3];"), "array<int, int>");
        assert_eq!(infer("['a' => 1, 'b' => 2];"), "array<string, int>");
        assert_eq!(infer("[1, 'x'];"), "array<int, int|string>");
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
        assert_eq!(infer("1 <=> 2;"), "int");
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
        assert_eq!(infer("true ? 1 : 'x';"), "int|string");
        assert_eq!(infer_with("$x ?? 0;", &[("x", Type::Nullable(Box::new(Type::String)))], None), "string|int");
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
        assert_eq!(infer("match($x) { 1 => 'a', default => 2 };"), "string|int");
    }
}
