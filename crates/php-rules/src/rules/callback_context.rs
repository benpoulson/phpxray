//! Context-sensitive diagnostics for same-file named callbacks.
//!
//! The file-level type map stays global and conservative: named callback bodies
//! are not re-recorded there because the same function/method can be called from
//! multiple contexts. This module builds a temporary contextual map for one
//! resolvable callback call site and runs a narrow set of existing diagnostics
//! over the target body.

use crate::{
    function_like,
    members::{self, MemberAccessResolver, ResolveStatus},
    walk, FileAnalysis, RuleEntry,
};
use php_ast::{
    Arg, ClassDecl, Expr, ExprKind, FunctionDecl, Member, MemberName, MethodDecl, Name, Program,
    Stmt,
};
use php_diagnostics::Diagnostic;
use php_infer::{arrays, contextual_body_type_map, TypeMap};
use php_reflect::{reflect_class, reflect_function, FunctionReflection, MethodReflection};
use php_resolve::{for_each_region, Resolution, Scope};
use php_types::Type;
use std::collections::{HashMap, HashSet};

type SpanKey = (u32, u32);
type DedupeKey = (SpanKey, SpanKey, &'static str, String);

pub(crate) static RULES: &[RuleEntry] = &[
    RuleEntry {
        name: "callbackContext.member",
        level: 0,
        run: run_member,
    },
    RuleEntry {
        name: "callbackContext.returnType",
        level: 3,
        run: run_return,
    },
    RuleEntry {
        name: "callbackContext.argumentType",
        level: 5,
        run: run_argument,
    },
];

fn run_member(fa: &FileAnalysis) -> Vec<Diagnostic> {
    collect(fa, ContextRule::Member)
}

fn run_return(fa: &FileAnalysis) -> Vec<Diagnostic> {
    collect(fa, ContextRule::Return)
}

fn run_argument(fa: &FileAnalysis) -> Vec<Diagnostic> {
    collect(fa, ContextRule::Argument)
}

#[derive(Clone, Copy)]
enum ContextRule {
    Member,
    Return,
    Argument,
}

struct FunctionBody<'a> {
    scope: Scope,
    decl: &'a FunctionDecl,
    refl: FunctionReflection,
}

struct MethodBody<'a> {
    scope: Scope,
    class_fqn: String,
    decl: &'a MethodDecl,
    refl: MethodReflection,
}

struct BodyIndex<'a> {
    functions: HashMap<String, FunctionBody<'a>>,
    methods: HashMap<(String, String), MethodBody<'a>>,
}

#[derive(Clone, Copy)]
enum CallbackBody<'a> {
    Function(&'a FunctionBody<'a>),
    Method(&'a MethodBody<'a>),
}

struct CallbackContext<'a> {
    call_key: SpanKey,
    body: CallbackBody<'a>,
    inferred: Vec<Type>,
}

struct Overlay<'a> {
    fa: &'a FileAnalysis<'a>,
    scope: &'a Scope,
    types: TypeMap,
    native_types: TypeMap,
}

impl Overlay<'_> {
    fn type_of(&self, e: &Expr) -> Type {
        self.types
            .get(&span_key(e))
            .or_else(|| self.fa.types.get(&span_key(e)))
            .cloned()
            .unwrap_or(Type::Mixed)
    }

    fn native_type_of(&self, e: &Expr) -> Type {
        self.native_types
            .get(&span_key(e))
            .or_else(|| self.fa.native_types.get(&span_key(e)))
            .cloned()
            .unwrap_or(Type::Mixed)
    }

    fn accepts(&self, e: &Expr, target: &Type, native_target: &Type) -> bool {
        if !function_like::type_mismatch_reportable(
            self.fa.reflection,
            &self.type_of(e),
            target,
            self.fa.check_nullables,
            self.fa.report_maybes,
        ) {
            return true;
        }
        if self.fa.treat_phpdoc_types_as_certain {
            return false;
        }
        !function_like::type_mismatch_reportable(
            self.fa.reflection,
            &self.native_type_of(e),
            native_target,
            self.fa.check_nullables,
            self.fa.report_maybes,
        )
    }
}

fn collect(fa: &FileAnalysis, rule: ContextRule) -> Vec<Diagnostic> {
    let bodies = BodyIndex::new(fa);
    let contexts = callback_contexts(fa, &bodies);
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    for cx in contexts {
        let overlay = cx.overlay(fa);
        let mut local = Vec::new();
        match rule {
            ContextRule::Member => {
                check_method_not_found(&overlay, cx.body.body(), &mut local);
                check_property_not_found(&overlay, cx.body.body(), &mut local);
            }
            ContextRule::Return => check_return_type(&overlay, cx.body, &mut local),
            ContextRule::Argument => check_argument_types(&overlay, cx.body.body(), &mut local),
        }
        dedupe_from(&mut local, &mut seen, cx.call_key);
        out.extend(local);
    }
    out
}

impl<'a> BodyIndex<'a> {
    fn new(fa: &'a FileAnalysis<'a>) -> Self {
        let mut functions = HashMap::new();
        let mut methods = HashMap::new();
        for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
            for st in region {
                collect_bodies_stmt(fa, scope, st, &mut functions, &mut methods);
            }
        });
        Self { functions, methods }
    }

    fn function(&self, fqn: &str) -> Option<&FunctionBody<'a>> {
        self.functions.get(&fqn_key(fqn))
    }

    fn method(&self, class_fqn: &str, method: &str) -> Option<&MethodBody<'a>> {
        self.methods
            .get(&(fqn_key(class_fqn), method.to_ascii_lowercase()))
    }
}

fn collect_bodies_stmt<'a>(
    fa: &'a FileAnalysis<'a>,
    scope: &Scope,
    st: &'a Stmt,
    functions: &mut HashMap<String, FunctionBody<'a>>,
    methods: &mut HashMap<(String, String), MethodBody<'a>>,
) {
    match &st.kind {
        php_ast::StmtKind::Function(f) => {
            let refl = reflect_function(scope, fa.interner, f);
            functions.insert(
                fqn_key(&refl.fqn),
                FunctionBody {
                    scope: scope.clone(),
                    decl: f,
                    refl,
                },
            );
        }
        php_ast::StmtKind::Class(c) => collect_class_bodies(fa, scope, c, methods),
        php_ast::StmtKind::Block(body)
        | php_ast::StmtKind::Namespace {
            body: Some(body), ..
        } => {
            for child in body {
                collect_bodies_stmt(fa, scope, child, functions, methods);
            }
        }
        php_ast::StmtKind::If {
            then, elseifs, els, ..
        } => {
            collect_bodies_stmt(fa, scope, then, functions, methods);
            for elseif in elseifs {
                collect_bodies_stmt(fa, scope, &elseif.body, functions, methods);
            }
            if let Some(els) = els {
                collect_bodies_stmt(fa, scope, els, functions, methods);
            }
        }
        php_ast::StmtKind::While { body, .. }
        | php_ast::StmtKind::DoWhile { body, .. }
        | php_ast::StmtKind::For { body, .. }
        | php_ast::StmtKind::Foreach { body, .. }
        | php_ast::StmtKind::Declare {
            body: Some(body), ..
        } => collect_bodies_stmt(fa, scope, body, functions, methods),
        php_ast::StmtKind::Switch { cases, .. } => {
            for case in cases {
                for child in &case.body {
                    collect_bodies_stmt(fa, scope, child, functions, methods);
                }
            }
        }
        php_ast::StmtKind::Try {
            body,
            catches,
            finally,
        } => {
            for child in body {
                collect_bodies_stmt(fa, scope, child, functions, methods);
            }
            for catch in catches {
                for child in &catch.body {
                    collect_bodies_stmt(fa, scope, child, functions, methods);
                }
            }
            if let Some(finally) = finally {
                for child in finally {
                    collect_bodies_stmt(fa, scope, child, functions, methods);
                }
            }
        }
        _ => {}
    }
}

fn collect_class_bodies<'a>(
    fa: &'a FileAnalysis<'a>,
    scope: &Scope,
    class: &'a ClassDecl,
    methods: &mut HashMap<(String, String), MethodBody<'a>>,
) {
    let Some(name) = class.name else { return };
    let class_fqn = scope.qualify(fa.interner.resolve(name));
    let refl = reflect_class(scope, fa.interner, &class_fqn, class);
    for member in &class.members {
        let Member::Method(method) = member else {
            continue;
        };
        if method.body.is_none() {
            continue;
        }
        let method_name = fa.interner.resolve(method.name);
        let Some(mr) = refl
            .methods
            .iter()
            .find(|m| !m.magic && m.name.eq_ignore_ascii_case(method_name))
            .cloned()
        else {
            continue;
        };
        methods.insert(
            (fqn_key(&class_fqn), method_name.to_ascii_lowercase()),
            MethodBody {
                scope: scope.clone(),
                class_fqn: class_fqn.clone(),
                decl: method,
                refl: mr,
            },
        );
    }
}

impl<'a> CallbackContext<'a> {
    fn overlay(&self, fa: &'a FileAnalysis<'a>) -> Overlay<'a> {
        let (scope, class, params, body) = match self.body {
            CallbackBody::Function(f) => (&f.scope, None, &f.refl.params, f.decl.body.as_slice()),
            CallbackBody::Method(m) => (
                &m.scope,
                Some(m.class_fqn.clone()),
                &m.refl.params,
                m.decl.body.as_deref().unwrap_or(&[]),
            ),
        };
        let types = contextual_body_type_map(
            fa.reflection,
            scope,
            fa.interner,
            class.clone(),
            params,
            &self.inferred,
            false,
            body,
        );
        let native_types = contextual_body_type_map(
            fa.reflection,
            scope,
            fa.interner,
            class,
            params,
            &self.inferred,
            true,
            body,
        );
        Overlay {
            fa,
            scope,
            types,
            native_types,
        }
    }
}

impl<'a> CallbackBody<'a> {
    fn body(&self) -> &'a [Stmt] {
        match self {
            CallbackBody::Function(f) => &f.decl.body,
            CallbackBody::Method(m) => m.decl.body.as_deref().unwrap_or(&[]),
        }
    }

    fn params(&self) -> &'a [php_reflect::ParamReflection] {
        match self {
            CallbackBody::Function(f) => &f.refl.params,
            CallbackBody::Method(m) => &m.refl.params,
        }
    }

    fn return_type(&self) -> (&'a Type, &'a Type, String) {
        match self {
            CallbackBody::Function(f) => (
                &f.refl.return_type,
                &f.refl.native_return,
                format!("function {}()", f.refl.fqn),
            ),
            CallbackBody::Method(m) => (
                &m.refl.return_type,
                &m.refl.native_return,
                format!("{}::{}()", m.class_fqn, m.refl.name),
            ),
        }
    }
}

fn callback_contexts<'a>(
    fa: &'a FileAnalysis<'a>,
    bodies: &'a BodyIndex<'a>,
) -> Vec<CallbackContext<'a>> {
    let mut out = Vec::new();
    for_each_region(&fa.program.stmts, fa.interner, |scope, region| {
        let program = Program {
            stmts: region.to_vec(),
        };
        walk::for_each_expr(&program, &mut |e| {
            collect_expr_context(fa, scope, bodies, e, &mut out);
        });
    });
    out
}

fn collect_expr_context<'a>(
    fa: &'a FileAnalysis<'a>,
    scope: &Scope,
    bodies: &'a BodyIndex<'a>,
    e: &Expr,
    out: &mut Vec<CallbackContext<'a>>,
) {
    match &e.kind {
        ExprKind::Call { callee, args } => {
            if let Some((callback, inferred)) = builtin_callback_seed(fa, scope, callee, args) {
                push_context(fa, scope, bodies, e, callback, inferred, out);
            }
        }
        ExprKind::MethodCall {
            recv, method, args, ..
        } => {
            if let Some((callback, inferred)) = collection_callback_seed(fa, recv, method, args) {
                push_context(fa, scope, bodies, e, callback, inferred, out);
            }
        }
        _ => {}
    }
}

fn push_context<'a>(
    fa: &'a FileAnalysis<'a>,
    scope: &Scope,
    bodies: &'a BodyIndex<'a>,
    call: &Expr,
    callback: &Arg,
    inferred: Vec<Type>,
    out: &mut Vec<CallbackContext<'a>>,
) {
    if matches!(
        peel_paren(&callback.value).kind,
        ExprKind::Closure(_) | ExprKind::ArrowFn(_)
    ) {
        return;
    }
    let Some(body) = resolve_callback_body(fa, scope, bodies, &callback.value) else {
        return;
    };
    if !context_changes_params(body.params(), &inferred) {
        return;
    }
    out.push(CallbackContext {
        call_key: span_key(call),
        body,
        inferred,
    });
}

fn builtin_callback_seed<'a>(
    fa: &'a FileAnalysis<'a>,
    scope: &Scope,
    callee: &Expr,
    args: &'a [Arg],
) -> Option<(&'a Arg, Vec<Type>)> {
    if !args_are_plain_positional(args) {
        return None;
    }
    let ExprKind::Name(name) = &callee.kind else {
        return None;
    };
    let func = function_from_name(fa, scope, name)?;
    if !func.builtin {
        return None;
    }
    match last_segment(&func.fqn).to_ascii_lowercase().as_str() {
        "array_map" => {
            let callback = args.first()?;
            let inferred = args
                .iter()
                .skip(1)
                .map(|arg| array_value_type(&fa.type_of(&arg.value)))
                .collect();
            Some((callback, inferred))
        }
        "array_filter" => {
            let array = args.first()?;
            let callback = args.get(1)?;
            let value = array_value_type(&fa.type_of(&array.value));
            let key = array_key_type(&fa.type_of(&array.value));
            let inferred = array_filter_callback_params(args, value, key)?;
            Some((callback, inferred))
        }
        "array_walk" => {
            let array = args.first()?;
            let callback = args.get(1)?;
            let mut inferred = vec![
                array_value_type(&fa.type_of(&array.value)),
                array_key_type(&fa.type_of(&array.value)),
            ];
            if let Some(user_arg) = args.get(2) {
                inferred.push(fa.type_of(&user_arg.value));
            }
            Some((callback, inferred))
        }
        "usort" | "uasort" => {
            let array = args.first()?;
            let callback = args.get(1)?;
            let value = array_value_type(&fa.type_of(&array.value));
            Some((callback, vec![value.clone(), value]))
        }
        "uksort" => {
            let array = args.first()?;
            let callback = args.get(1)?;
            let key = array_key_type(&fa.type_of(&array.value));
            Some((callback, vec![key.clone(), key]))
        }
        "preg_replace_callback" => {
            let callback = args.get(1)?;
            preg_replace_callback_flags_are_plain(args)
                .then(|| (callback, vec![preg_match_array_type()]))
        }
        _ => None,
    }
}

fn collection_callback_seed<'a>(
    fa: &'a FileAnalysis<'a>,
    recv: &Expr,
    method: &MemberName,
    args: &'a [Arg],
) -> Option<(&'a Arg, Vec<Type>)> {
    if !args_are_plain_positional(args) {
        return None;
    }
    let MemberName::Ident(sym) = method else {
        return None;
    };
    let callback = args.first()?;
    let kind = collection_method(fa.interner.resolve(*sym))?;
    let recv_ty = fa.type_of(recv);
    let (key, value) = collection_key_value(fa, &recv_ty)?;
    let inferred = match kind {
        CollectionMethod::Map
        | CollectionMethod::Filter
        | CollectionMethod::Each
        | CollectionMethod::Walk => vec![value, key],
        CollectionMethod::Reduce => {
            let carry = args
                .get(1)
                .map(|arg| fa.type_of(&arg.value))
                .unwrap_or(Type::Mixed);
            vec![carry, value, key]
        }
    };
    Some((callback, inferred))
}

fn resolve_callback_body<'a>(
    fa: &'a FileAnalysis<'a>,
    scope: &Scope,
    bodies: &'a BodyIndex<'a>,
    e: &Expr,
) -> Option<CallbackBody<'a>> {
    match &peel_paren(e).kind {
        ExprKind::Str(bytes) => literal_str(bytes)
            .and_then(|name| function_fqn_from_text(fa, scope, &name))
            .and_then(|fqn| bodies.function(&fqn))
            .map(CallbackBody::Function),
        ExprKind::Variable(_) => match fa.type_of(e) {
            Type::LiteralString(name) => function_fqn_from_text(fa, scope, &name)
                .and_then(|fqn| bodies.function(&fqn))
                .map(CallbackBody::Function),
            ty => invokable_body(fa, bodies, &ty),
        },
        ExprKind::Array { items, .. } => callable_array_body(fa, scope, bodies, items),
        ExprKind::Call { callee, args } if is_first_class_callable(args) => {
            let ExprKind::Name(name) = &callee.kind else {
                return None;
            };
            function_from_name(fa, scope, name)
                .and_then(|f| bodies.function(&f.fqn))
                .map(CallbackBody::Function)
        }
        ExprKind::MethodCall {
            recv, method, args, ..
        } if is_first_class_callable(args) => method_body_from_receiver(fa, bodies, recv, method),
        ExprKind::StaticCall {
            class,
            method,
            args,
        } if is_first_class_callable(args) => {
            let class = class_fqn_from_expr(fa, scope, class)?;
            let MemberName::Ident(sym) = method else {
                return None;
            };
            method_body_from_class_name(fa, bodies, &class, fa.interner.resolve(*sym))
        }
        _ => invokable_body(fa, bodies, &fa.type_of(e)),
    }
}

fn callable_array_body<'a>(
    fa: &'a FileAnalysis<'a>,
    scope: &Scope,
    bodies: &'a BodyIndex<'a>,
    items: &[php_ast::ArrayItem],
) -> Option<CallbackBody<'a>> {
    let [target, method] = items else {
        return None;
    };
    if target.spread || method.spread || target.key.is_some() || method.key.is_some() {
        return None;
    }
    let target = target.value.as_ref()?;
    let method_name = method.value.as_ref().and_then(literal_string_expr)?;
    if let Some(class) = class_fqn_from_callable_array_target(fa, scope, target) {
        return method_body_from_class_name(fa, bodies, &class, &method_name);
    }
    method_body_from_receiver_name(fa, bodies, target, &method_name)
}

fn method_body_from_receiver<'a>(
    fa: &'a FileAnalysis<'a>,
    bodies: &'a BodyIndex<'a>,
    recv: &Expr,
    method: &MemberName,
) -> Option<CallbackBody<'a>> {
    let MemberName::Ident(sym) = method else {
        return None;
    };
    method_body_from_receiver_name(fa, bodies, recv, fa.interner.resolve(*sym))
}

fn method_body_from_receiver_name<'a>(
    fa: &'a FileAnalysis<'a>,
    bodies: &'a BodyIndex<'a>,
    recv: &Expr,
    method: &str,
) -> Option<CallbackBody<'a>> {
    let recv_ty = fa.type_of(recv);
    let found = fa
        .reflection
        .find_method_on_type(&recv_ty, method)
        .or_else(|| {
            members::sole_class(&recv_ty).and_then(|fqn| fa.reflection.find_method(&fqn, method))
        })?;
    bodies
        .method(&found.declaring_class, &found.member.name)
        .map(CallbackBody::Method)
}

fn method_body_from_class_name<'a>(
    fa: &'a FileAnalysis<'a>,
    bodies: &'a BodyIndex<'a>,
    class: &str,
    method: &str,
) -> Option<CallbackBody<'a>> {
    let found = fa.reflection.find_method(class, method)?;
    bodies
        .method(&found.declaring_class, &found.member.name)
        .map(CallbackBody::Method)
}

fn invokable_body<'a>(
    fa: &'a FileAnalysis<'a>,
    bodies: &'a BodyIndex<'a>,
    ty: &Type,
) -> Option<CallbackBody<'a>> {
    let fqn = members::sole_class(ty)?;
    let found = fa.reflection.find_method(&fqn, "__invoke")?;
    bodies
        .method(&found.declaring_class, &found.member.name)
        .map(CallbackBody::Method)
}

fn check_method_not_found(overlay: &Overlay, body: &[Stmt], out: &mut Vec<Diagnostic>) {
    let resolver = MemberAccessResolver::new(overlay.fa);
    for_each_body_expr(body, |e| {
        let ExprKind::MethodCall { recv, method, .. } = &e.kind else {
            return;
        };
        let MemberName::Ident(sym) = method else {
            return;
        };
        let recv_ty = overlay.type_of(recv);
        if overlay.fa.check_nullables && super::type_contains_null(&recv_ty) {
            return;
        }
        let method_name = overlay.fa.interner.resolve(*sym);
        if let ResolveStatus::Unknown = resolver.instance_method(&recv_ty, method_name) {
            let Some(fqn) = members::sole_class(&recv_ty) else {
                return;
            };
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("Call to an undefined method {fqn}::{method_name}()."),
                )
                .with_code("method.notFound"),
            );
        }
    });
}

fn check_property_not_found(overlay: &Overlay, body: &[Stmt], out: &mut Vec<Diagnostic>) {
    let resolver = MemberAccessResolver::new(overlay.fa);
    let assign_targets = assignment_target_spans(body);
    let suppressed = undefined_allowed_property_spans(body);
    for_each_body_expr(body, |e| {
        let ExprKind::Prop {
            base,
            name,
            nullsafe,
        } = &e.kind
        else {
            return;
        };
        if *nullsafe {
            return;
        }
        let key = span_key(e);
        if assign_targets.contains(&key) || suppressed.contains(&key) {
            return;
        }
        let MemberName::Ident(sym) = name else {
            return;
        };
        let base_ty = overlay.type_of(base);
        let prop = overlay.fa.interner.resolve(*sym);
        if let ResolveStatus::Unknown = resolver.instance_property(&base_ty, prop, false) {
            let Some(fqn) = members::sole_class(&base_ty) else {
                return;
            };
            out.push(
                Diagnostic::error(
                    e.span,
                    format!("Access to an undefined property {fqn}::${prop}."),
                )
                .with_code("property.notFound"),
            );
        }
    });
}

fn check_argument_types(overlay: &Overlay, body: &[Stmt], out: &mut Vec<Diagnostic>) {
    for_each_body_expr(body, |e| match &e.kind {
        ExprKind::Call { callee, args } => {
            check_function_call_args(overlay, callee, args, out);
        }
        ExprKind::MethodCall {
            recv, method, args, ..
        } => {
            check_method_call_args(overlay, recv, method, args, out);
        }
        _ => {}
    });
}

fn check_function_call_args(
    overlay: &Overlay,
    callee: &Expr,
    args: &[Arg],
    out: &mut Vec<Diagnostic>,
) {
    if !args_are_plain_positional(args) {
        return;
    }
    let ExprKind::Name(name) = &callee.kind else {
        return;
    };
    let Some(func) = function_from_name(overlay.fa, overlay.scope, name) else {
        return;
    };
    if func.builtin && !func.params.iter().any(|p| p.variadic) && args.len() > func.params.len() {
        return;
    }
    for (i, arg) in args.iter().enumerate() {
        let Some(param) = func.params.get(i) else {
            break;
        };
        if param.variadic {
            break;
        }
        let given = overlay.type_of(&arg.value);
        if !overlay.accepts(&arg.value, &param.ty, &param.native_ty) {
            out.push(
                Diagnostic::error(
                    arg.value.span,
                    format!(
                        "Parameter #{} ${} of function {} expects {}, {given} given.",
                        i + 1,
                        param.name,
                        func.fqn,
                        param.ty
                    ),
                )
                .with_code("argument.type"),
            );
        }
    }
}

fn check_method_call_args(
    overlay: &Overlay,
    recv: &Expr,
    method: &MemberName,
    args: &[Arg],
    out: &mut Vec<Diagnostic>,
) {
    if !args_are_plain_positional(args) {
        return;
    }
    let MemberName::Ident(sym) = method else {
        return;
    };
    let recv_ty = overlay.type_of(recv);
    let method_name = overlay.fa.interner.resolve(*sym);
    let Some(found) = overlay
        .fa
        .reflection
        .find_method_on_type(&recv_ty, method_name)
        .or_else(|| {
            members::sole_class(&recv_ty)
                .and_then(|fqn| overlay.fa.reflection.find_method(&fqn, method_name))
        })
    else {
        return;
    };
    if found.member.magic {
        return;
    }
    let short = members::sole_class(&recv_ty).unwrap_or(found.declaring_class);
    for (i, arg) in args.iter().enumerate() {
        let Some(param) = found.member.params.get(i) else {
            break;
        };
        if param.variadic {
            break;
        }
        let given = overlay.type_of(&arg.value);
        if !overlay.accepts(&arg.value, &param.ty, &param.native_ty) {
            out.push(
                Diagnostic::error(
                    arg.value.span,
                    format!(
                        "Parameter #{} ${} of method {short}::{method_name}() expects {}, {given} given.",
                        i + 1,
                        param.name,
                        param.ty
                    ),
                )
                .with_code("argument.type"),
            );
        }
    }
}

fn check_return_type(overlay: &Overlay, body: CallbackBody, out: &mut Vec<Diagnostic>) {
    let (declared, native_declared, label) = body.return_type();
    if skip_return(declared) {
        return;
    }
    function_like::collect_returns(body.body(), |expr| {
        let Some(expr) = expr else {
            return;
        };
        let actual = overlay.type_of(expr);
        if !function_like::type_mismatch_reportable(
            overlay.fa.reflection,
            &actual,
            declared,
            overlay.fa.check_nullables,
            overlay.fa.report_maybes,
        ) {
            return;
        }
        if !overlay.fa.treat_phpdoc_types_as_certain
            && !function_like::type_mismatch_reportable(
                overlay.fa.reflection,
                &overlay.native_type_of(expr),
                native_declared,
                overlay.fa.check_nullables,
                overlay.fa.report_maybes,
            )
        {
            return;
        }
        function_like::push_return_type_error(out, expr, &label, declared, &actual);
    });
}

fn for_each_body_expr(body: &[Stmt], mut f: impl FnMut(&Expr)) {
    for st in body {
        walk::for_each_expr_in_scope(st, &mut f);
    }
}

fn dedupe_from(out: &mut Vec<Diagnostic>, seen: &mut HashSet<DedupeKey>, call_key: SpanKey) {
    out.retain(|d| {
        let key = (
            call_key,
            span_key_raw(d.primary),
            d.code.unwrap_or(""),
            d.message.clone(),
        );
        seen.insert(key)
    });
}

fn context_changes_params(params: &[php_reflect::ParamReflection], inferred: &[Type]) -> bool {
    params.iter().enumerate().any(|(i, p)| {
        !p.explicit
            && inferred
                .get(i)
                .is_some_and(|ty| !callback_seed_is_imprecise(ty))
    })
}

fn callback_seed_is_imprecise(t: &Type) -> bool {
    match t {
        Type::Mixed | Type::ExplicitMixed | Type::Unknown(_) | Type::TemplateVar(_) => true,
        Type::Nullable(inner) | Type::List(inner) | Type::ClassString(Some(inner)) => {
            callback_seed_is_imprecise(inner)
        }
        Type::Union(parts) | Type::Intersection(parts) => {
            parts.iter().all(callback_seed_is_imprecise)
        }
        Type::Array(Some(kv)) | Type::Iterable(Some(kv)) => {
            callback_seed_is_imprecise(&kv.0) && callback_seed_is_imprecise(&kv.1)
        }
        Type::Callable(Some(sig)) => {
            callback_seed_is_imprecise(&sig.ret)
                && sig.params.iter().all(callback_seed_is_imprecise)
        }
        Type::Named { .. } => false,
        Type::Shape { fields, .. } => fields.iter().all(|f| callback_seed_is_imprecise(&f.ty)),
        _ => false,
    }
}

fn function_from_name<'a>(
    fa: &'a FileAnalysis<'a>,
    scope: &Scope,
    name: &Name,
) -> Option<&'a FunctionReflection> {
    match scope.resolve_function(name) {
        Resolution::Fqn(fqn) => fa.reflection.function(&fqn),
        Resolution::Fallback { namespaced, global } => fa
            .reflection
            .function(&namespaced)
            .or_else(|| fa.reflection.function(&global)),
        _ => None,
    }
}

fn function_fqn_from_text(fa: &FileAnalysis, scope: &Scope, name: &str) -> Option<String> {
    if name.contains('\\') || name.starts_with('\\') {
        return fa.reflection.function(name).map(|f| f.fqn.clone());
    }
    fa.reflection
        .function(name)
        .or_else(|| fa.reflection.function(&scope.qualify(name)))
        .map(|f| f.fqn.clone())
}

fn class_fqn_from_callable_array_target(
    fa: &FileAnalysis,
    scope: &Scope,
    e: &Expr,
) -> Option<String> {
    match &peel_paren(e).kind {
        ExprKind::ClassConst { class, name } => {
            let MemberName::Ident(sym) = name else {
                return None;
            };
            if !fa.interner.resolve(*sym).eq_ignore_ascii_case("class") {
                return None;
            }
            class_fqn_from_expr(fa, scope, class)
        }
        ExprKind::Str(bytes) => {
            literal_str(bytes).and_then(|name| class_fqn_from_text(fa, scope, &name))
        }
        _ => None,
    }
}

fn class_fqn_from_expr(fa: &FileAnalysis, scope: &Scope, e: &Expr) -> Option<String> {
    match &peel_paren(e).kind {
        ExprKind::Name(name) => match scope.resolve_class(name) {
            Resolution::Fqn(fqn) => Some(fqn),
            Resolution::LateStatic(_)
            | Resolution::BuiltinType(_)
            | Resolution::Fallback { .. } => None,
        },
        _ => class_fqn_from_type_expr(fa, e),
    }
}

fn class_fqn_from_type_expr(fa: &FileAnalysis, e: &Expr) -> Option<String> {
    members::sole_class(&fa.type_of(e))
}

fn class_fqn_from_text(fa: &FileAnalysis, scope: &Scope, name: &str) -> Option<String> {
    if name.contains('\\') || name.starts_with('\\') {
        return fa.reflection.class(name).map(|c| c.fqn.clone());
    }
    fa.reflection
        .class(name)
        .or_else(|| fa.reflection.class(&scope.qualify(name)))
        .map(|c| c.fqn.clone())
}

fn collection_key_value(fa: &FileAnalysis, recv_ty: &Type) -> Option<(Type, Type)> {
    let Type::Named { fqn, args } = peel_nullable(recv_ty) else {
        return None;
    };
    fa.reflection.class(fqn)?;
    match args.len() {
        1 => Some((Type::Mixed, args[0].clone())),
        n if n >= 2 => Some((args[0].clone(), args[1].clone())),
        _ => None,
    }
}

fn peel_nullable(t: &Type) -> &Type {
    match t {
        Type::Nullable(inner) => peel_nullable(inner),
        _ => t,
    }
}

#[derive(Clone, Copy)]
enum CollectionMethod {
    Map,
    Filter,
    Each,
    Walk,
    Reduce,
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

fn array_filter_callback_params(args: &[Arg], value: Type, key: Type) -> Option<Vec<Type>> {
    match args.get(2).map(|a| &a.value) {
        None => Some(vec![value]),
        Some(mode) => match array_filter_mode(mode)? {
            ArrayFilterMode::Value => Some(vec![value]),
            ArrayFilterMode::Key => Some(vec![key]),
            ArrayFilterMode::Both => Some(vec![value, key]),
        },
    }
}

enum ArrayFilterMode {
    Value,
    Key,
    Both,
}

fn array_filter_mode(e: &Expr) -> Option<ArrayFilterMode> {
    match int_lit(e) {
        Some(0) => return Some(ArrayFilterMode::Value),
        Some(1) => return Some(ArrayFilterMode::Both),
        Some(2) => return Some(ArrayFilterMode::Key),
        Some(_) => return None,
        None => {}
    }
    let ExprKind::Name(n) = &peel_paren(e).kind else {
        return None;
    };
    match global_const_text(&n.text)? {
        "ARRAY_FILTER_USE_BOTH" => Some(ArrayFilterMode::Both),
        "ARRAY_FILTER_USE_KEY" => Some(ArrayFilterMode::Key),
        _ => None,
    }
}

fn preg_replace_callback_flags_are_plain(args: &[Arg]) -> bool {
    match args.get(5).map(|a| &a.value) {
        None => true,
        Some(flags) => int_lit(flags) == Some(0),
    }
}

fn preg_match_array_type() -> Type {
    Type::Array(Some(Box::new((
        Type::union(vec![Type::Int, Type::String]),
        Type::String,
    ))))
}

fn array_value_type(ty: &Type) -> Type {
    arrays::array_value_type(ty).unwrap_or(Type::Mixed)
}

fn array_key_type(ty: &Type) -> Type {
    arrays::array_key_type(ty).unwrap_or(Type::Mixed)
}

fn assignment_target_spans(body: &[Stmt]) -> HashSet<(u32, u32)> {
    let mut spans = HashSet::new();
    for_each_body_expr(body, |e| {
        let (ExprKind::Assign { target, .. } | ExprKind::AssignRef { target, .. }) = &e.kind else {
            return;
        };
        if matches!(&target.kind, ExprKind::Prop { .. }) {
            spans.insert(span_key(target));
        }
    });
    spans
}

fn undefined_allowed_property_spans(body: &[Stmt]) -> HashSet<(u32, u32)> {
    let mut spans = HashSet::new();
    for_each_body_expr(body, |e| match &e.kind {
        ExprKind::Isset(vars) => {
            for v in vars {
                mark_property_subtree(v, &mut spans);
            }
        }
        ExprKind::Empty(inner) => mark_property_subtree(inner, &mut spans),
        ExprKind::Coalesce { lhs, .. } => mark_property_subtree(lhs, &mut spans),
        ExprKind::AssignOp {
            op: php_ast::BinOp::Coalesce,
            target,
            ..
        } => mark_property_subtree(target, &mut spans),
        _ => {}
    });
    spans
}

fn mark_property_subtree(expr: &Expr, spans: &mut HashSet<(u32, u32)>) {
    walk::for_each_subexpr(expr, &mut |e| {
        if matches!(e.kind, ExprKind::Prop { .. }) {
            spans.insert(span_key(e));
        }
    });
}

fn literal_string_expr(e: &Expr) -> Option<String> {
    match &peel_paren(e).kind {
        ExprKind::Str(bytes) => literal_str(bytes),
        _ => None,
    }
}

fn literal_str(bytes: &[u8]) -> Option<String> {
    std::str::from_utf8(bytes).ok().map(str::to_string)
}

fn is_first_class_callable(args: &[Arg]) -> bool {
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

fn int_lit(e: &Expr) -> Option<i64> {
    match &peel_paren(e).kind {
        ExprKind::Int(n) => Some(*n),
        _ => None,
    }
}

fn global_const_text(text: &str) -> Option<&str> {
    let stripped = text.strip_prefix('\\').unwrap_or(text);
    (!stripped.contains('\\')).then_some(stripped)
}

fn last_segment(name: &str) -> &str {
    name.trim_start_matches('\\')
        .rsplit('\\')
        .next()
        .unwrap_or(name)
}

fn fqn_key(fqn: &str) -> String {
    fqn.trim_start_matches('\\').to_ascii_lowercase()
}

fn span_key(e: &Expr) -> (u32, u32) {
    span_key_raw(e.span)
}

fn span_key_raw(span: php_span::Span) -> (u32, u32) {
    let r = span.range();
    (r.start as u32, r.end as u32)
}

fn skip_return(t: &Type) -> bool {
    matches!(
        t,
        Type::Mixed | Type::ExplicitMixed | Type::Void | Type::Never
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::codes;

    #[test]
    fn method_not_found_inside_named_function_array_map_callback_is_flagged() {
        let src = r#"<?php
            class User {}
            /** @param list<User> $users */
            function run(array $users): void {
                array_map('cb', $users);
            }
            function cb($u): void {
                $u->missing();
            }
        "#;
        assert_eq!(codes(src, run_member), ["method.notFound"]);
    }

    #[test]
    fn property_not_found_inside_same_file_method_callback_is_flagged() {
        let src = r#"<?php
            class User {}
            class Runner {
                /** @param list<User> $users */
                public function run(array $users): void {
                    array_map([$this, 'cb'], $users);
                }
                public function cb($u): void {
                    echo $u->missing;
                }
            }
        "#;
        assert_eq!(codes(src, run_member), ["property.notFound"]);
    }

    #[test]
    fn argument_type_inside_named_array_filter_callback_is_flagged() {
        let src = r#"<?php
            class User {}
            function takes_string(string $s): void {}
            /** @param list<User> $users */
            function run(array $users): void {
                array_filter($users, 'cb');
            }
            function cb($u): bool {
                takes_string($u);
                return true;
            }
        "#;
        assert_eq!(codes(src, run_argument), ["argument.type"]);
    }

    #[test]
    fn return_type_inside_named_callback_uses_seeded_param() {
        let src = r#"<?php
            class User {}
            /** @param list<User> $users */
            function run(array $users): void {
                array_map('cb', $users);
            }
            function cb($u): string {
                return $u;
            }
        "#;
        assert_eq!(codes(src, run_return), ["return.type"]);
    }

    #[test]
    fn collection_map_named_method_callback_is_checked() {
        let src = r#"<?php
            /**
             * @template T
             */
            class Collection {
                /** @param callable(T): mixed $cb @return Collection<mixed> */
                public function map(callable $cb): self {}
            }
            class User {}
            class Runner {
                /** @param Collection<User> $users */
                public function run(Collection $users): void {
                    $users->map([$this, 'cb']);
                }
                public function cb($u): void {
                    $u->missing();
                }
            }
        "#;
        assert_eq!(codes(src, run_member), ["method.notFound"]);
    }

    #[test]
    fn explicit_callback_param_is_not_overridden() {
        let src = r#"<?php
            class User {}
            /** @param list<User> $users */
            function run(array $users): void {
                array_map('cb', $users);
            }
            function cb(string $u): void {
                strlen($u);
            }
        "#;
        assert!(codes(src, run_argument).is_empty());
        assert!(codes(src, run_member).is_empty());
    }

    #[test]
    fn dynamic_callback_target_is_skipped() {
        let src = r#"<?php
            class User {}
            /** @param list<User> $users */
            function run(array $users, callable $cb): void {
                array_map($cb, $users);
            }
            function cb($u): void {
                $u->missing();
            }
        "#;
        assert!(codes(src, run_member).is_empty());
    }

    #[test]
    fn direct_closure_callback_is_not_duplicated_by_context_rule() {
        let src = r#"<?php
            class User {}
            /** @param list<User> $users */
            function run(array $users): void {
                array_map(fn($u) => $u->missing(), $users);
            }
        "#;
        assert!(codes(src, run_member).is_empty());
    }
}
