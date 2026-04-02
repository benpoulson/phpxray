//! Cap #5: **definedness analysis** — which variable *reads* may hit an
//! undefined (or possibly-undefined) variable.
//!
//! A flow-sensitive forward pass over each scope (the global region, each
//! function/method body, each closure/arrow-fn) tracking, per variable, a small
//! lattice: `Definite` (assigned on every path so far), `Maybe` (assigned on
//! some), or absent (never assigned). A variable *read* whose name is absent is
//! a definite "Undefined variable"; `Maybe` is "might not be defined".
//!
//! PHP has many ways to introduce a variable, so the analysis is deliberately
//! conservative — it **bails on a whole scope** that uses an escape hatch it
//! can't model (`extract`/`parse_str`, variable-variables `$$x`/`${expr}`,
//! `eval`, `include`). Function/method **by-ref arguments** also define a
//! variable, which we can't always resolve, so a bare `$var` passed directly to
//! a call is never reported. The result: under-reporting rather than false
//! positives (the project's rule for the whole type layer).

use php_ast::{
    ArrowFn, BinOp, ClosureExpr, Expr, ExprKind, FunctionDecl, MethodDecl, Member, Param, Stmt,
    StmtKind,
};
use php_intern::Interner;
use php_span::Span;
use std::collections::HashMap;

/// Definedness lattice value for a variable that is present in the environment.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Def {
    Definite,
    Maybe,
}

type Env = HashMap<String, Def>;

/// A variable read that may be undefined.
pub struct UndefVar {
    pub span: Span,
    pub name: String,
    /// `true` = definitely undefined; `false` = possibly undefined (some paths).
    pub definite: bool,
}

/// PHP superglobals + always-available variables — never reported.
const ALWAYS_DEFINED: &[&str] = &[
    "GLOBALS", "_SERVER", "_GET", "_POST", "_FILES", "_COOKIE", "_SESSION", "_REQUEST", "_ENV",
    "this", "http_response_header", "argc", "argv", "php_errormsg",
];

/// Function names whose presence means we can't reason about definedness in the
/// enclosing scope (they can introduce or require arbitrary variables).
const ESCAPE_FUNCTIONS: &[&str] = &[
    "extract", "parse_str", "mb_parse_str", "get_defined_vars", "compact", "eval",
];

/// Analyse a whole program and return the possibly-undefined variable reads.
pub fn undefined_variables(program: &php_ast::Program, interner: &Interner) -> Vec<UndefVar> {
    let mut a = Analyzer { interner, out: Vec::new() };
    // The global region is its own scope; nested function/class decls recurse.
    a.analyze_scope(&program.stmts, Env::new());
    a.out
}

struct Analyzer<'a> {
    interner: &'a Interner,
    out: Vec<UndefVar>,
}

impl Analyzer<'_> {
    /// Analyse one scope's statement list with `seed` as the initial environment
    /// (params/captures already inserted). Bails (records nothing for this scope)
    /// if the scope uses an escape hatch.
    fn analyze_scope(&mut self, body: &[Stmt], seed: Env) {
        if stmts_have_escape_hatch(body, self.interner) {
            // Still descend into nested declarations (their own scopes are checked
            // independently and may be clean).
            self.descend_only(body);
            return;
        }
        let mut env = seed;
        self.exec_block(body, &mut env);
    }

    /// When a scope is skipped, we still analyse nested function/class bodies.
    fn descend_only(&mut self, body: &[Stmt]) {
        for s in body {
            match &s.kind {
                StmtKind::Function(f) => self.analyze_function(f),
                StmtKind::Class(c) => self.analyze_class(c),
                StmtKind::Namespace { body: Some(b), .. } => self.descend_only(b),
                _ => {}
            }
        }
    }

    fn analyze_function(&mut self, f: &FunctionDecl) {
        let mut seed = Env::new();
        seed_params(&mut seed, &f.params, self.interner);
        self.analyze_scope(&f.body, seed);
    }

    fn analyze_class(&mut self, c: &php_ast::ClassDecl) {
        for m in &c.members {
            if let Member::Method(md) = m {
                self.analyze_method(md);
            }
        }
    }

    fn analyze_method(&mut self, m: &MethodDecl) {
        let Some(body) = &m.body else { return };
        let mut seed = Env::new();
        seed_params(&mut seed, &m.params, self.interner);
        self.analyze_scope(body, seed);
    }

    // --- statement execution --------------------------------------------

    fn exec_block(&mut self, stmts: &[Stmt], env: &mut Env) {
        for s in stmts {
            self.exec_stmt(s, env);
        }
    }

    fn exec_stmt(&mut self, s: &Stmt, env: &mut Env) {
        match &s.kind {
            StmtKind::Expr(e) => self.read_expr(e, env),
            StmtKind::Echo(es) => es.iter().for_each(|e| self.read_expr(e, env)),
            StmtKind::Return(Some(e)) => self.read_expr(e, env),
            StmtKind::Block(b) => self.exec_block(b, env),
            StmtKind::If { cond, then, elseifs, els } => {
                self.read_expr(cond, env);
                self.exec_if(then, elseifs, els.as_deref(), env);
            }
            StmtKind::While { cond, body } => {
                self.read_expr(cond, env);
                self.exec_loop(body, env);
            }
            StmtKind::DoWhile { body, cond } => {
                // The body always runs at least once.
                self.exec_stmt(body, env);
                self.read_expr(cond, env);
            }
            StmtKind::For { init, cond, update, body } => {
                for e in init {
                    self.read_expr(e, env);
                }
                for e in cond.iter().chain(update) {
                    self.read_expr(e, env);
                }
                self.exec_loop(body, env);
            }
            StmtKind::Foreach { subject, key, value, body, .. } => {
                self.read_expr(subject, env);
                // The loop may run zero times: variables bound here and in the body
                // are only `Maybe` afterwards.
                let mut body_env = env.clone();
                if let Some(k) = key {
                    self.bind(k, &mut body_env);
                }
                self.bind(value, &mut body_env);
                self.exec_stmt(body, &mut body_env);
                *env = merge(vec![env.clone(), body_env]);
            }
            StmtKind::Switch { subject, cases } => {
                self.read_expr(subject, env);
                let base = env.clone();
                let mut envs = vec![base.clone()];
                for case in cases {
                    if let Some(t) = &case.test {
                        self.read_expr(t, env);
                    }
                    let mut ce = base.clone();
                    self.exec_block(&case.body, &mut ce);
                    envs.push(ce);
                }
                *env = merge(envs);
            }
            StmtKind::Try { body, catches, finally } => {
                self.exec_block(body, env);
                for c in catches {
                    let mut ce = env.clone();
                    if let Some(v) = c.var {
                        ce.insert(self.interner.resolve(v).to_string(), Def::Definite);
                    }
                    self.exec_block(&c.body, &mut ce);
                }
                if let Some(f) = finally {
                    self.exec_block(f, env);
                }
            }
            StmtKind::Global(vars) | StmtKind::Unset(vars) => {
                // `global $x` defines; `unset($x)` — leave defined (conservative:
                // unsetting then reading is rare and undefining risks FPs).
                for v in vars {
                    if let ExprKind::Variable(sym) = &v.kind {
                        env.insert(self.interner.resolve(*sym).to_string(), Def::Definite);
                    }
                }
            }
            StmtKind::StaticVars(vars) => {
                for sv in vars {
                    if let Some(d) = &sv.default {
                        self.read_expr(d, env);
                    }
                    env.insert(self.interner.resolve(sv.name).to_string(), Def::Definite);
                }
            }
            // Nested declarations open their own scope.
            StmtKind::Function(f) => self.analyze_function(f),
            StmtKind::Class(c) => self.analyze_class(c),
            StmtKind::Namespace { body: Some(b), .. } => self.exec_block(b, env),
            StmtKind::Declare { body: Some(b), .. } => self.exec_stmt(b, env),
            _ => {}
        }
    }

    fn exec_if(&mut self, then: &Stmt, elseifs: &[php_ast::ElseIf], els: Option<&Stmt>, env: &mut Env) {
        let base = env.clone();
        let mut envs: Vec<Env> = Vec::new();

        let mut then_env = base.clone();
        self.exec_stmt(then, &mut then_env);
        if !always_terminates(then) {
            envs.push(then_env);
        }

        for ei in elseifs {
            let mut ee = base.clone();
            self.read_expr(&ei.cond, &mut ee);
            self.exec_stmt(&ei.body, &mut ee);
            if !always_terminates(&ei.body) {
                envs.push(ee);
            }
        }

        match els {
            Some(e) => {
                let mut ee = base.clone();
                self.exec_stmt(e, &mut ee);
                if !always_terminates(e) {
                    envs.push(ee);
                }
            }
            // No else: a path where nothing was assigned.
            None => envs.push(base.clone()),
        }

        *env = if envs.is_empty() { base } else { merge(envs) };
    }

    /// A loop body that may run zero or more times.
    fn exec_loop(&mut self, body: &Stmt, env: &mut Env) {
        let mut be = env.clone();
        self.exec_stmt(body, &mut be);
        *env = merge(vec![env.clone(), be]);
    }

    // --- expressions ----------------------------------------------------

    /// Evaluate `e` in *read* position: record undefined variable reads and
    /// process any assignments it performs.
    fn read_expr(&mut self, e: &Expr, env: &mut Env) {
        match &e.kind {
            ExprKind::Variable(sym) => {
                let name = self.interner.resolve(*sym);
                self.check_read(name, e.span, env);
            }
            ExprKind::Assign { target, rhs } => {
                self.read_expr(rhs, env);
                self.bind(target, env);
            }
            ExprKind::AssignRef { target, rhs } => {
                // `$a =& $b` makes both `$a` and `$b` defined — referencing an
                // undefined variable *creates* it (no warning), so bind both.
                self.bind(rhs, env);
                self.bind(target, env);
            }
            ExprKind::AssignOp { op, target, rhs } => {
                self.read_expr(rhs, env);
                // `$x += 1` reads `$x` (warns if undefined); `$x ??= 1` does not.
                // But `$a[$k] += 1` only reads the *key* — the base auto-vivifies
                // — so only a bare-variable target is read here; `bind` handles
                // the index read + base define for `$a[…]`/`$o->p`.
                if *op != BinOp::Coalesce && matches!(target.kind, ExprKind::Variable(_)) {
                    self.read_expr(target, env);
                }
                self.bind(target, env);
            }
            // `$x++`/`--$x` on an undefined var auto-vivifies it (PHP warns, but
            // to stay false-positive-safe on later reads we treat it as a define).
            ExprKind::PreInc(t) | ExprKind::PreDec(t) | ExprKind::PostInc(t) | ExprKind::PostDec(t) => {
                self.bind(t, env);
            }
            // `$arr[]` (append) only ever appears in a write/by-ref context and
            // auto-vivifies its base — never an undefined read.
            ExprKind::Index { base, index: None } => self.bind(base, env),
            // An array literal: a `&$x` element references (and so defines) `$x`;
            // ordinary elements are reads.
            ExprKind::Array { items, .. } => {
                for it in items {
                    if let Some(k) = &it.key {
                        self.read_expr(k, env);
                    }
                    if let Some(v) = &it.value {
                        if it.by_ref {
                            self.bind(v, env);
                        } else {
                            self.read_expr(v, env);
                        }
                    }
                }
            }
            // `isset(...)` / `empty(...)` / `$x ?? ...` suppress undefined reads on
            // their operands — skip them entirely (conservative; may miss reads of
            // index expressions, but never a false positive).
            ExprKind::Isset(_) | ExprKind::Empty(_) => {}
            ExprKind::Coalesce { rhs, .. } => self.read_expr(rhs, env),
            // A bare `$var` argument might be a by-ref parameter (which defines
            // it), so don't report it; still recurse into compound arguments.
            ExprKind::Call { callee, args } => {
                self.read_expr(callee, env);
                self.read_call_args(args, env);
            }
            ExprKind::MethodCall { recv, args, .. } => {
                self.read_expr(recv, env);
                self.read_call_args(args, env);
            }
            ExprKind::StaticCall { class, args, .. } => {
                self.read_expr(class, env);
                self.read_call_args(args, env);
            }
            // Closures/arrow-fns: a new scope. Arrow fns auto-capture the
            // enclosing variables by value; closures only capture `use` vars.
            ExprKind::Closure(c) => self.read_closure(c, env),
            ExprKind::ArrowFn(a) => self.read_arrow(a, env.clone()),
            _ => walk_children(e, &mut |c| self.read_expr(c, env)),
        }
    }

    fn read_call_args(&mut self, args: &[php_ast::Arg], env: &mut Env) {
        for arg in args {
            // A direct `$var` argument may be passed by reference, which *defines*
            // it (e.g. `preg_match(…, $m)`). We don't always know the callee, so
            // conservatively treat a bare-variable argument as a define rather
            // than a read — never a false positive on it or on later reads.
            if matches!(arg.value.kind, ExprKind::Variable(_)) {
                self.bind(&arg.value, env);
                continue;
            }
            self.read_expr(&arg.value, env);
        }
    }

    fn read_closure(&mut self, c: &ClosureExpr, outer: &mut Env) {
        let mut seed = Env::new();
        for u in &c.uses {
            let name = self.interner.resolve(u.name).to_string();
            if u.by_ref {
                // `use (&$x)` defines `$x` in the *outer* scope too.
                outer.insert(name.clone(), Def::Definite);
            } else {
                // by-value capture reads the outer variable.
                self.check_read(&name, Span::new(0, 0), outer);
            }
            seed.insert(name, Def::Definite);
        }
        seed_params(&mut seed, &c.params, self.interner);
        self.analyze_scope(&c.body, seed);
    }

    fn read_arrow(&mut self, a: &ArrowFn, mut seed: Env) {
        // Arrow fns capture the enclosing scope by value.
        seed_params(&mut seed, &a.params, self.interner);
        if expr_escape(&a.body, self.interner) {
            return;
        }
        self.read_expr(&a.body, &mut seed);
    }

    /// Record a read of `$name` if it isn't definitely defined.
    fn check_read(&mut self, name: &str, span: Span, env: &Env) {
        if ALWAYS_DEFINED.contains(&name) {
            return;
        }
        match env.get(name) {
            Some(Def::Definite) => {}
            Some(Def::Maybe) => {
                self.out.push(UndefVar { span, name: name.to_string(), definite: false })
            }
            None => self.out.push(UndefVar { span, name: name.to_string(), definite: true }),
        }
    }

    /// Process an assignment *target*, defining the variables it introduces.
    fn bind(&mut self, target: &Expr, env: &mut Env) {
        match &target.kind {
            ExprKind::Variable(sym) => {
                env.insert(self.interner.resolve(*sym).to_string(), Def::Definite);
            }
            // `list($a, $b) = …` / `[$a, $b] = …`.
            ExprKind::Array { items, .. } => {
                for it in items {
                    if let Some(v) = &it.value {
                        self.bind(v, env);
                    }
                    if let Some(k) = &it.key {
                        self.read_expr(k, env);
                    }
                }
            }
            // `$a[…] = v` auto-vivifies `$a`, so it *defines* the base variable.
            ExprKind::Index { base, index } => {
                if let Some(i) = index {
                    self.read_expr(i, env);
                }
                self.bind(base, env);
            }
            // `$obj->p = v` requires `$obj` to already be an object — read it.
            ExprKind::Prop { base, .. } => self.read_expr(base, env),
            ExprKind::StaticProp { .. } => {}
            // Anything else in target position — evaluate as a read.
            _ => self.read_expr(target, env),
        }
    }
}

/// Seed function/closure parameters as definitely defined.
fn seed_params(env: &mut Env, params: &[Param], interner: &Interner) {
    for p in params {
        env.insert(interner.resolve(p.name).to_string(), Def::Definite);
    }
}

/// Merge several branch environments: a variable is `Definite` only if it is
/// `Definite` in *every* branch; `Maybe` if present in some.
fn merge(envs: Vec<Env>) -> Env {
    if envs.len() == 1 {
        return envs.into_iter().next().unwrap();
    }
    let n = envs.len();
    let mut present: HashMap<String, (usize, usize)> = HashMap::new(); // name -> (present_count, definite_count)
    for env in &envs {
        for (name, d) in env {
            let e = present.entry(name.clone()).or_insert((0, 0));
            e.0 += 1;
            if *d == Def::Definite {
                e.1 += 1;
            }
        }
    }
    let mut out = Env::new();
    for (name, (present_count, definite_count)) in present {
        let d = if present_count == n && definite_count == n { Def::Definite } else { Def::Maybe };
        out.insert(name, d);
    }
    out
}

/// Whether `s` always leaves the current block (so its env doesn't flow past it).
fn always_terminates(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Return(_) | StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Goto(_) => true,
        StmtKind::Expr(e) => matches!(&e.kind, ExprKind::Throw(_) | ExprKind::Exit(_)),
        StmtKind::Block(b) => b.last().is_some_and(always_terminates),
        StmtKind::If { then, elseifs, els: Some(els), .. } => {
            always_terminates(then)
                && elseifs.iter().all(|ei| always_terminates(&ei.body))
                && always_terminates(els)
        }
        _ => false,
    }
}

// --- escape-hatch detection ------------------------------------------------

fn stmts_have_escape_hatch(stmts: &[Stmt], interner: &Interner) -> bool {
    stmts.iter().any(|s| stmt_escape(s, interner))
}

fn stmt_escape(s: &Stmt, interner: &Interner) -> bool {
    match &s.kind {
        // Do NOT descend into nested scopes — they're analysed independently.
        StmtKind::Function(_) | StmtKind::Class(_) => false,
        _ => {
            let mut found = false;
            walk_stmt_nodes(s, &mut |n| {
                if !found {
                    found = match n {
                        Node::Expr(e) => expr_escape(e, interner),
                        Node::Block(b) => stmts_have_escape_hatch(b, interner),
                    };
                }
            });
            found
        }
    }
}

fn expr_escape(e: &Expr, interner: &Interner) -> bool {
    match &e.kind {
        // Dynamic variables and eval/include can define arbitrary names.
        ExprKind::VariableVariable(_) | ExprKind::DollarBrace(_) | ExprKind::Eval(_) | ExprKind::Include { .. } => true,
        ExprKind::Call { callee, .. } => {
            if let ExprKind::Name(n) = &callee.kind {
                let last = n.text.rsplit('\\').next().unwrap_or(&n.text).to_ascii_lowercase();
                if ESCAPE_FUNCTIONS.contains(&last.as_str()) {
                    return true;
                }
            }
            any_child_escapes(e, interner)
        }
        // Nested scopes are analysed independently — don't let their hatches bail
        // the enclosing scope.
        ExprKind::Closure(_) | ExprKind::ArrowFn(_) => false,
        _ => any_child_escapes(e, interner),
    }
}

fn any_child_escapes(e: &Expr, interner: &Interner) -> bool {
    let mut found = false;
    walk_children(e, &mut |c| {
        if !found {
            found = expr_escape(c, interner);
        }
    });
    found
}

// --- tiny child walkers (local to this module) -----------------------------

/// Apply `f` to each immediate sub-expression of `e` (not crossing into nested
/// function/closure scopes — those are handled explicitly).
fn walk_children(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    use ExprKind::*;
    match &e.kind {
        Binary { lhs, rhs, .. } => {
            f(lhs);
            f(rhs);
        }
        Unary { expr, .. } | Cast { expr, .. } | Clone(expr) | Print(expr) | Throw(expr)
        | ErrorSuppress(expr) | Empty(expr) | Paren(expr) | PreInc(expr) | PreDec(expr)
        | PostInc(expr) | PostDec(expr) | DollarBrace(expr) | VariableVariable(expr) => f(expr),
        Assign { target, rhs } | AssignRef { target, rhs } => {
            f(target);
            f(rhs);
        }
        AssignOp { target, rhs, .. } => {
            f(target);
            f(rhs);
        }
        Ternary { cond, then, els } => {
            f(cond);
            if let Some(t) = then {
                f(t);
            }
            f(els);
        }
        Coalesce { lhs, rhs } => {
            f(lhs);
            f(rhs);
        }
        Instanceof { expr, class } => {
            f(expr);
            f(class);
        }
        Index { base, index } => {
            f(base);
            if let Some(i) = index {
                f(i);
            }
        }
        Prop { base, .. } => f(base),
        StaticProp { class, .. } | ClassConst { class, .. } => f(class),
        New { class, args } => {
            f(class);
            args.iter().for_each(|a| f(&a.value));
        }
        Call { callee, args } => {
            f(callee);
            args.iter().for_each(|a| f(&a.value));
        }
        MethodCall { recv, args, .. } => {
            f(recv);
            args.iter().for_each(|a| f(&a.value));
        }
        StaticCall { class, args, .. } => {
            f(class);
            args.iter().for_each(|a| f(&a.value));
        }
        Array { items, .. } => {
            for it in items {
                if let Some(k) = &it.key {
                    f(k);
                }
                if let Some(v) = &it.value {
                    f(v);
                }
            }
        }
        Isset(es) => es.iter().for_each(&mut *f),
        Match { subject, arms } => {
            f(subject);
            for arm in arms {
                if let Some(conds) = &arm.conds {
                    conds.iter().for_each(&mut *f);
                }
                f(&arm.body);
            }
        }
        Interpolated(parts) => parts.iter().for_each(&mut *f),
        Yield { key, value } => {
            if let Some(k) = key {
                f(k);
            }
            if let Some(v) = value {
                f(v);
            }
        }
        YieldFrom(e) => f(e),
        Exit(Some(e)) => f(e),
        Include { expr, .. } => f(expr),
        Eval(e) => f(e),
        _ => {}
    }
}

/// A child of a statement, for escape-hatch scanning.
enum Node<'a> {
    Expr(&'a Expr),
    Block(&'a [Stmt]),
}

/// Apply `f` to each top-level expression / nested block of statement `s`.
fn walk_stmt_nodes(s: &Stmt, f: &mut dyn FnMut(Node)) {
    use StmtKind::*;
    match &s.kind {
        Expr(e) | Return(Some(e)) => f(Node::Expr(e)),
        Echo(es) => es.iter().for_each(|e| f(Node::Expr(e))),
        Block(b) => f(Node::Block(b)),
        If { cond, then, elseifs, els } => {
            f(Node::Expr(cond));
            f(Node::Block(one(then)));
            for ei in elseifs {
                f(Node::Expr(&ei.cond));
                f(Node::Block(one(&ei.body)));
            }
            if let Some(e) = els {
                f(Node::Block(one(e)));
            }
        }
        While { cond, body } => {
            f(Node::Expr(cond));
            f(Node::Block(one(body)));
        }
        DoWhile { body, cond } => {
            f(Node::Block(one(body)));
            f(Node::Expr(cond));
        }
        For { init, cond, update, body } => {
            init.iter().chain(cond).chain(update).for_each(|e| f(Node::Expr(e)));
            f(Node::Block(one(body)));
        }
        Foreach { subject, key, value, body, .. } => {
            f(Node::Expr(subject));
            if let Some(k) = key {
                f(Node::Expr(k));
            }
            f(Node::Expr(value));
            f(Node::Block(one(body)));
        }
        Switch { subject, cases } => {
            f(Node::Expr(subject));
            for c in cases {
                if let Some(t) = &c.test {
                    f(Node::Expr(t));
                }
                f(Node::Block(&c.body));
            }
        }
        Try { body, catches, finally } => {
            f(Node::Block(body));
            for c in catches {
                f(Node::Block(&c.body));
            }
            if let Some(fb) = finally {
                f(Node::Block(fb));
            }
        }
        Global(es) | Unset(es) => es.iter().for_each(|e| f(Node::Expr(e))),
        StaticVars(vs) => vs.iter().filter_map(|v| v.default.as_ref()).for_each(|e| f(Node::Expr(e))),
        Namespace { body: Some(b), .. } => f(Node::Block(b)),
        Declare { body: Some(b), .. } => f(Node::Block(one(b))),
        _ => {}
    }
}

/// View a single statement as a one-element slice (deref-coerces `&Box<Stmt>`).
fn one(s: &Stmt) -> &[Stmt] {
    std::slice::from_ref(s)
}
