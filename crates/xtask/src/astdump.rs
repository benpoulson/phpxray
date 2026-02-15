//! Canonical AST dumper for the structural differential against PHP's Zend AST.
//!
//! Emits the *exact* same s-expression form as `crates/xtask/php/dump_ast.php`
//! (the real Zend AST via the `php-ast` extension). Any difference is a real
//! parser divergence. Node kinds/flags/child-orders mirror Zend precisely.

use php_ast::*;
use php_intern::Interner;

enum C {
    N(String, Vec<(&'static str, C)>),
    Int(i64),
    Float(f64),
    Str(String),
    Null,
}

pub fn dump(program: &Program, _src: &str, interner: &Interner) -> String {
    let d = Dumper { i: interner };
    let root = C::N("STMT_LIST".into(), d.stmt_list(&program.stmts));
    let mut out = String::new();
    render(&root, 0, &mut out);
    out
}

fn render(c: &C, ind: usize, out: &mut String) {
    let p = "  ".repeat(ind);
    match c {
        C::N(head, kids) => {
            out.push_str(&format!("{p}({head}\n"));
            for (k, child) in kids {
                let key = if k.is_empty() { String::new() } else { format!("{k}=") };
                out.push_str(&format!("{p}  {key}\n"));
                render(child, ind + 2, out);
            }
            out.push_str(&format!("{p})\n"));
        }
        C::Int(v) => out.push_str(&format!("{p}{v}\n")),
        C::Float(v) => out.push_str(&format!("{p}{}\n", fmt_float(*v))),
        C::Str(s) => out.push_str(&format!("{p}\"{}\"\n", escape(s))),
        C::Null => out.push_str(&format!("{p}null\n")),
    }
}

fn fmt_float(v: f64) -> String {
    if v.is_nan() {
        return "NAN".into();
    }
    if v.is_infinite() {
        return if v > 0.0 { "INF".into() } else { "-INF".into() };
    }
    // Match PHP var_export: shortest round-trip, but `1.0E+121` style exponents.
    let s = format!("{v:?}");
    if let Some(epos) = s.find(['e', 'E']) {
        let (mant, rest) = s.split_at(epos);
        let exp = &rest[1..];
        let mant = if mant.contains('.') { mant.to_string() } else { format!("{mant}.0") };
        let (sign, digits) = match exp.strip_prefix('-') {
            Some(d) => ("-", d),
            None => ("+", exp.strip_prefix('+').unwrap_or(exp)),
        };
        format!("{mant}E{sign}{digits}")
    } else {
        s
    }
}

fn escape(s: &str) -> String {
    let mut o = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '\\' => o.push_str("\\\\"),
            '"' => o.push_str("\\\""),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            _ => o.push(ch),
        }
    }
    o
}

fn node(head: &str, kids: Vec<(&'static str, C)>) -> C {
    C::N(head.to_string(), kids)
}
fn head(name: &str, flag: u32) -> String {
    if flag != 0 { format!("{name}#{flag}") } else { name.to_string() }
}

struct Dumper<'a> {
    i: &'a Interner,
}

impl<'a> Dumper<'a> {
    fn sym(&self, s: php_intern::Symbol) -> String {
        self.i.resolve(s).to_string()
    }

    // --- statements -------------------------------------------------------

    fn stmt_list(&self, stmts: &[Stmt]) -> Vec<(&'static str, C)> {
        let mut out = Vec::new();
        for s in stmts {
            for c in self.stmt(s) {
                out.push(("", c));
            }
        }
        out
    }

    /// STMT_LIST for a body: unwrap a block, else wrap a single statement.
    fn body(&self, s: &Stmt) -> C {
        match &s.kind {
            StmtKind::Block(b) => C::N("STMT_LIST".into(), self.stmt_list(b)),
            _ => C::N("STMT_LIST".into(), self.stmt(s).into_iter().map(|c| ("", c)).collect()),
        }
    }

    fn stmt(&self, s: &Stmt) -> Vec<C> {
        match &s.kind {
            StmtKind::Expr(e) => vec![self.expr(e)],
            StmtKind::Echo(es) => es.iter().map(|e| node("ECHO", vec![("expr", self.expr(e))])).collect(),
            StmtKind::Return(v) => vec![node("RETURN", vec![("expr", self.opt(v.as_ref()))])],
            StmtKind::Block(b) => vec![C::N("STMT_LIST".into(), self.stmt_list(b))],
            StmtKind::Nop => vec![],
            StmtKind::InlineHtml(s) => vec![node("ECHO", vec![("expr", C::Str(s.clone()))])],
            StmtKind::HaltCompiler(off) => vec![node("HALT_COMPILER", vec![("offset", C::Int(*off as i64))])],
            StmtKind::Break(l) => vec![node("BREAK", vec![("depth", self.opt(l.as_ref()))])],
            StmtKind::Continue(l) => vec![node("CONTINUE", vec![("depth", self.opt(l.as_ref()))])],
            StmtKind::Global(vs) => vs.iter().map(|v| node("GLOBAL", vec![("var", self.expr(v))])).collect(),
            StmtKind::Unset(vs) => vs.iter().map(|v| node("UNSET", vec![("var", self.expr(v))])).collect(),
            StmtKind::StaticVars(vs) => vs
                .iter()
                .map(|v| {
                    node(
                        "STATIC",
                        vec![
                            ("var", node("VAR", vec![("name", C::Str(self.sym(v.name)))])),
                            ("default", v.default.as_ref().map(|d| self.expr(d)).unwrap_or(C::Null)),
                        ],
                    )
                })
                .collect(),
            StmtKind::Goto(l) => vec![node("GOTO", vec![("label", C::Str(self.sym(*l)))])],
            StmtKind::Label(l) => vec![node("LABEL", vec![("name", C::Str(self.sym(*l)))])],
            StmtKind::If { cond, then, elseifs, els } => {
                let mut elems =
                    vec![("", node("IF_ELEM", vec![("cond", self.expr(cond)), ("stmts", self.body(then))]))];
                for ei in elseifs {
                    elems.push((
                        "",
                        node("IF_ELEM", vec![("cond", self.expr(&ei.cond)), ("stmts", self.body(&ei.body))]),
                    ));
                }
                if let Some(e) = els {
                    elems.push(("", node("IF_ELEM", vec![("cond", C::Null), ("stmts", self.body(e))])));
                }
                vec![C::N("IF".into(), elems)]
            }
            StmtKind::While { cond, body } => {
                vec![node("WHILE", vec![("cond", self.expr(cond)), ("stmts", self.body(body))])]
            }
            StmtKind::DoWhile { body, cond } => {
                vec![node("DO_WHILE", vec![("stmts", self.body(body)), ("cond", self.expr(cond))])]
            }
            StmtKind::For { init, cond, update, body } => vec![node(
                "FOR",
                vec![
                    ("init", self.expr_list(init)),
                    ("cond", self.expr_list(cond)),
                    ("loop", self.expr_list(update)),
                    ("stmts", self.body(body)),
                ],
            )],
            StmtKind::Foreach { subject, key, value, by_ref, body } => {
                let val = if *by_ref { node("REF", vec![("var", self.expr(value))]) } else { self.expr(value) };
                vec![node(
                    "FOREACH",
                    vec![
                        ("expr", self.expr(subject)),
                        ("value", val),
                        ("key", key.as_ref().map(|k| self.expr(k)).unwrap_or(C::Null)),
                        ("stmts", self.body(body)),
                    ],
                )]
            }
            StmtKind::Switch { subject, cases } => {
                let arms: Vec<_> = cases
                    .iter()
                    .map(|c| {
                        (
                            "",
                            node(
                                "SWITCH_CASE",
                                vec![
                                    ("cond", c.test.as_ref().map(|e| self.expr(e)).unwrap_or(C::Null)),
                                    ("stmts", C::N("STMT_LIST".into(), self.stmt_list(&c.body))),
                                ],
                            ),
                        )
                    })
                    .collect();
                vec![node(
                    "SWITCH",
                    vec![("cond", self.expr(subject)), ("stmts", C::N("SWITCH_LIST".into(), arms))],
                )]
            }
            StmtKind::Try { body, catches, finally } => {
                let cs: Vec<_> = catches
                    .iter()
                    .map(|c| {
                        let names: Vec<_> = c.types.iter().map(|t| ("", self.name_ref(t))).collect();
                        (
                            "",
                            node(
                                "CATCH",
                                vec![
                                    ("class", C::N("NAME_LIST".into(), names)),
                                    ("var", c.var.map(|v| node("VAR", vec![("name", C::Str(self.sym(v)))])).unwrap_or(C::Null)),
                                    ("stmts", C::N("STMT_LIST".into(), self.stmt_list(&c.body))),
                                ],
                            ),
                        )
                    })
                    .collect();
                vec![node(
                    "TRY",
                    vec![
                        ("try", C::N("STMT_LIST".into(), self.stmt_list(body))),
                        ("catches", C::N("CATCH_LIST".into(), cs)),
                        ("finally", finally.as_ref().map(|f| C::N("STMT_LIST".into(), self.stmt_list(f))).unwrap_or(C::Null)),
                    ],
                )]
            }
            StmtKind::Namespace { name, body } => vec![node(
                "NAMESPACE",
                vec![
                    ("name", name.as_ref().map(|n| C::Str(n.text.trim_start_matches('\\').to_string())).unwrap_or(C::Null)),
                    ("stmts", body.as_ref().map(|b| C::N("STMT_LIST".into(), self.stmt_list(b))).unwrap_or(C::Null)),
                ],
            )],
            StmtKind::ConstDecl { consts, attrs } => {
                let mut cs: Vec<_> = consts
                    .iter()
                    .map(|e| ("", node("CONST_ELEM", vec![("name", C::Str(self.sym(e.name))), ("value", self.expr(&e.value))])))
                    .collect();
                if !attrs.is_empty() {
                    cs.push(("", self.attrs(attrs)));
                }
                vec![C::N("CONST_DECL".into(), cs)]
            }
            StmtKind::Declare { directives, body } => {
                let ds: Vec<_> = directives
                    .iter()
                    .map(|(n, v)| ("", node("CONST_ELEM", vec![("name", C::Str(self.sym(*n))), ("value", self.expr(v))])))
                    .collect();
                vec![node(
                    "DECLARE",
                    vec![
                        ("declares", C::N("CONST_DECL".into(), ds)),
                        ("stmts", body.as_ref().map(|b| self.body(b)).unwrap_or(C::Null)),
                    ],
                )]
            }
            StmtKind::Use(items) => self.use_decls(items),
            StmtKind::Function(f) => vec![self.func_decl(f)],
            StmtKind::Class(c) => vec![self.class_decl(c)],
            _ => vec![node("UNMAPPED_STMT", vec![])],
        }
    }

    fn use_decls(&self, items: &[UseItem]) -> Vec<C> {
        // Our parser flattens group use into per-item entries; emit a USE node
        // grouping consecutive same-kind items (approximates Zend; group-use
        // structure is refined later).
        let kind_flag = |k: UseKind| match k {
            UseKind::Class => 1,
            UseKind::Function => 2,
            UseKind::Const => 4,
        };
        let mut out = Vec::new();
        let elems: Vec<_> = items
            .iter()
            .map(|it| {
                ("", node("USE_ELEM", vec![
                    ("name", C::Str(it.name.text.trim_start_matches('\\').to_string())),
                    ("alias", it.alias.map(|a| C::Str(self.sym(a))).unwrap_or(C::Null)),
                ]))
            })
            .collect();
        let flag = items.first().map(|i| kind_flag(i.kind)).unwrap_or(1);
        out.push(C::N(head("USE", flag), elems));
        out
    }

    fn func_decl(&self, f: &FunctionDecl) -> C {
        let flag = if f.by_ref { 4096 } else { 0 } | gen_flag(&f.body);
        C::N(
            head("FUNC_DECL", flag),
            vec![
                ("name", C::Str(self.sym(f.name))),
                ("params", self.params(&f.params)),
                ("stmts", C::N("STMT_LIST".into(), self.stmt_list(&f.body))),
                ("returnType", self.opt_type(&f.return_type)),
                ("attributes", self.attrs(&f.attrs)),
            ],
        )
    }

    fn class_decl(&self, c: &ClassDecl) -> C {
        let flag = class_flag(c);
        let name_list = |this: &Self, ns: &[Name]| {
            if ns.is_empty() {
                C::Null
            } else {
                C::N("NAME_LIST".into(), ns.iter().map(|n| ("", this.name_ref(n))).collect())
            }
        };
        // php-ast puts interface parents in `implements` (extends stays null).
        let (extends, implements) = if c.kind == ClassKind::Interface {
            (C::Null, name_list(self, &c.extends))
        } else {
            (c.extends.first().map(|n| self.name_ref(n)).unwrap_or(C::Null), name_list(self, &c.implements))
        };
        let members: Vec<_> = c.members.iter().map(|m| ("", self.member_decl(m))).collect();
        C::N(
            head("CLASS", flag),
            vec![
                ("name", c.name.map(|n| C::Str(self.sym(n))).unwrap_or(C::Null)),
                ("extends", extends),
                ("implements", implements),
                ("stmts", C::N("STMT_LIST".into(), members)),
                ("attributes", self.attrs(&c.attrs)),
                ("type", self.opt_type(&c.backing)),
            ],
        )
    }

    fn member_decl(&self, m: &Member) -> C {
        match m {
            Member::Method(d) => {
                let gen = d.body.as_deref().map(gen_flag).unwrap_or(0);
                let flag = modifiers_flag(&d.modifiers, true) | if d.by_ref { 4096 } else { 0 } | gen;
                C::N(
                    head("METHOD", flag),
                    vec![
                        ("name", C::Str(self.sym(d.name))),
                        ("params", self.params(&d.params)),
                        ("stmts", d.body.as_ref().map(|b| C::N("STMT_LIST".into(), self.stmt_list(b))).unwrap_or(C::Null)),
                        ("returnType", self.opt_type(&d.return_type)),
                        ("attributes", self.attrs(&d.attrs)),
                    ],
                )
            }
            Member::Property(d) => {
                let elems: Vec<_> = d
                    .props
                    .iter()
                    .map(|p| {
                        (
                            "",
                            node("PROP_ELEM", vec![
                                ("name", C::Str(self.sym(p.name))),
                                ("default", p.default.as_ref().map(|e| self.expr(e)).unwrap_or(C::Null)),
                                ("hooks", self.hooks(&p.hooks)),
                            ]),
                        )
                    })
                    .collect();
                C::N(
                    head("PROP_GROUP", modifiers_flag(&d.modifiers, false)),
                    vec![
                        ("type", self.opt_type(&d.ty)),
                        ("props", C::N("PROP_DECL".into(), elems)),
                        ("attributes", self.attrs(&d.attrs)),
                    ],
                )
            }
            Member::ClassConst(d) => {
                let elems: Vec<_> = d
                    .consts
                    .iter()
                    .map(|c| ("", node("CONST_ELEM", vec![("name", C::Str(self.sym(c.name))), ("value", self.expr(&c.value))])))
                    .collect();
                C::N(
                    head("CLASS_CONST_GROUP", modifiers_flag(&d.modifiers, true)),
                    vec![
                        ("const", C::N("CLASS_CONST_DECL".into(), elems)),
                        ("attributes", self.attrs(&d.attrs)),
                        ("type", self.opt_type(&d.ty)),
                    ],
                )
            }
            Member::EnumCase(d) => node(
                "ENUM_CASE",
                vec![
                    ("name", C::Str(self.sym(d.name))),
                    ("expr", d.value.as_ref().map(|e| self.expr(e)).unwrap_or(C::Null)),
                    ("attributes", self.attrs(&d.attrs)),
                ],
            ),
            Member::TraitUse(d) => {
                let names: Vec<_> = d.traits.iter().map(|n| ("", self.name_ref(n))).collect();
                let adaptations = if d.adaptations.is_empty() {
                    C::Null
                } else {
                    C::N(
                        "TRAIT_ADAPTATIONS".into(),
                        d.adaptations.iter().map(|a| ("", self.trait_adaptation(a))).collect(),
                    )
                };
                node(
                    "USE_TRAIT",
                    vec![("traits", C::N("NAME_LIST".into(), names)), ("adaptations", adaptations)],
                )
            }
        }
    }

    fn params(&self, ps: &[Param]) -> C {
        let kids: Vec<_> = ps
            .iter()
            .map(|p| {
                let mut flag = modifiers_flag(&p.modifiers, false);
                if p.by_ref {
                    flag |= 8;
                }
                if p.variadic {
                    flag |= 16;
                }
                (
                    "",
                    C::N(
                        head("PARAM", flag),
                        vec![
                            ("type", self.opt_type(&p.ty)),
                            ("name", C::Str(self.sym(p.name))),
                            ("default", p.default.as_ref().map(|e| self.expr(e)).unwrap_or(C::Null)),
                            ("attributes", self.attrs(&p.attrs)),
                            ("hooks", self.hooks(&p.hooks)),
                        ],
                    ),
                )
            })
            .collect();
        C::N("PARAM_LIST".into(), kids)
    }

    fn trait_adaptation(&self, a: &TraitAdaptation) -> C {
        match a {
            TraitAdaptation::Precedence { class, method, insteadof } => {
                let mr = node("METHOD_REFERENCE", vec![("class", self.name_ref(class)), ("method", C::Str(self.sym(*method)))]);
                let names: Vec<_> = insteadof.iter().map(|n| ("", self.name_ref(n))).collect();
                node("TRAIT_PRECEDENCE", vec![("method", mr), ("insteadof", C::N("NAME_LIST".into(), names))])
            }
            TraitAdaptation::Alias { class, method, visibility, alias } => {
                let cls = class.as_ref().map(|c| self.name_ref(c)).unwrap_or(C::Null);
                let mr = node("METHOD_REFERENCE", vec![("class", cls), ("method", C::Str(self.sym(*method)))]);
                let flag = match visibility {
                    Some(Visibility::Public) => 1,
                    Some(Visibility::Protected) => 2,
                    Some(Visibility::Private) => 4,
                    None => 0,
                };
                C::N(
                    head("TRAIT_ALIAS", flag),
                    vec![("method", mr), ("alias", alias.map(|a| C::Str(self.sym(a))).unwrap_or(C::Null))],
                )
            }
        }
    }

    fn hooks(&self, hooks: &[PropertyHook]) -> C {
        if hooks.is_empty() {
            return C::Null;
        }
        C::N("STMT_LIST".into(), hooks.iter().map(|h| ("", self.property_hook(h))).collect())
    }

    fn property_hook(&self, h: &PropertyHook) -> C {
        let flag = modifiers_flag(&h.modifiers, false) | if h.by_ref { 4096 } else { 0 };
        let stmts = match &h.body {
            HookBody::Abstract => C::Null,
            HookBody::Block(b) => C::N("STMT_LIST".into(), self.stmt_list(b)),
            HookBody::Short(e) => node("PROPERTY_HOOK_SHORT_BODY", vec![("expr", self.expr(e))]),
        };
        C::N(
            head("PROPERTY_HOOK", flag),
            vec![
                ("name", C::Str(self.sym(h.name))),
                ("params", h.params.as_ref().map(|p| self.params(p)).unwrap_or(C::Null)),
                ("stmts", stmts),
                ("attributes", self.attrs(&h.attrs)),
            ],
        )
    }

    fn attrs(&self, groups: &[AttributeGroup]) -> C {
        if groups.is_empty() {
            return C::Null;
        }
        let gs: Vec<_> = groups
            .iter()
            .map(|g| {
                let a: Vec<_> = g
                    .attrs
                    .iter()
                    .map(|at| {
                        let args = match &at.args {
                            Some(a) => self.args(a),
                            None => C::Null,
                        };
                        ("", node("ATTRIBUTE", vec![("class", self.name_ref(&at.name)), ("args", args)]))
                    })
                    .collect();
                ("", C::N("ATTRIBUTE_GROUP".into(), a))
            })
            .collect();
        C::N("ATTRIBUTE_LIST".into(), gs)
    }

    // --- expressions ------------------------------------------------------

    fn opt(&self, e: Option<&Expr>) -> C {
        e.map(|e| self.expr(e)).unwrap_or(C::Null)
    }

    fn expr(&self, e: &Expr) -> C {
        match &e.kind {
            ExprKind::Int(n) => C::Int(*n),
            ExprKind::Float(f) => C::Float(*f),
            ExprKind::Str(v) => C::Str(v.clone()),
            ExprKind::Variable(s) => node("VAR", vec![("name", C::Str(self.sym(*s)))]),
            ExprKind::VariableVariable(inner) => node("VAR", vec![("name", self.expr(inner))]),
            ExprKind::Name(n) => self.const_or_magic(n),
            ExprKind::Binary { op, lhs, rhs } => self.binary(*op, lhs, rhs),
            ExprKind::Unary { op, expr } => self.unary(*op, expr),
            ExprKind::Assign { target, rhs } => node("ASSIGN", vec![("var", self.expr(target)), ("expr", self.expr(rhs))]),
            ExprKind::AssignRef { target, rhs } => node("ASSIGN_REF", vec![("var", self.expr(target)), ("expr", self.expr(rhs))]),
            ExprKind::AssignOp { op, target, rhs } => {
                C::N(head("ASSIGN_OP", binop_flag(*op)), vec![("var", self.expr(target)), ("expr", self.expr(rhs))])
            }
            ExprKind::Coalesce { lhs, rhs } => {
                C::N(head("BINARY_OP", 260), vec![("left", self.expr(lhs)), ("right", self.expr(rhs))])
            }
            ExprKind::Ternary { cond, then, els } => node(
                "CONDITIONAL",
                vec![("cond", self.expr(cond)), ("true", self.opt(then.as_deref())), ("false", self.expr(els))],
            ),
            ExprKind::Call { callee, args } => node("CALL", vec![("expr", self.class_or_name(callee)), ("args", self.args(args))]),
            ExprKind::MethodCall { recv, nullsafe, method, args } => node(
                if *nullsafe { "NULLSAFE_METHOD_CALL" } else { "METHOD_CALL" },
                vec![("expr", self.deref(recv)), ("method", self.member(method)), ("args", self.args(args))],
            ),
            ExprKind::StaticCall { class, method, args } => node(
                "STATIC_CALL",
                vec![("class", self.deref_class(class)), ("method", self.member(method)), ("args", self.args(args))],
            ),
            ExprKind::Index { base, index } => node("DIM", vec![("expr", self.deref(base)), ("dim", self.opt(index.as_deref()))]),
            ExprKind::Prop { base, nullsafe, name } => node(
                if *nullsafe { "NULLSAFE_PROP" } else { "PROP" },
                vec![("expr", self.deref(base)), ("prop", self.member(name))],
            ),
            ExprKind::StaticProp { class, name } => {
                // php-ast represents `Foo::$bar`'s property as the bare name string.
                let prop = match name {
                    MemberName::Var(s) | MemberName::Ident(s) => C::Str(self.sym(*s)),
                    MemberName::Expr(e) => self.expr(e),
                };
                node("STATIC_PROP", vec![("class", self.deref_class(class)), ("prop", prop)])
            }
            ExprKind::ClassConst { class, name } => {
                if let MemberName::Ident(s) = name {
                    if self.i.resolve(*s).eq_ignore_ascii_case("class") {
                        return node("CLASS_NAME", vec![("class", self.deref_class(class))]);
                    }
                }
                node("CLASS_CONST", vec![("class", self.deref_class(class)), ("const", self.member(name))])
            }
            ExprKind::New { class, args } => node("NEW", vec![("class", self.class_or_name(class)), ("args", self.args(args))]),
            ExprKind::NewAnon { class, args } => node("NEW", vec![("class", self.class_decl(class)), ("args", self.args(args))]),
            ExprKind::Array { items, syntax } => self.array(items, *syntax),
            ExprKind::Clone(e) => node("CLONE", vec![("expr", self.expr(e))]),
            ExprKind::Print(e) => node("PRINT", vec![("expr", self.expr(e))]),
            ExprKind::Throw(e) => node("THROW", vec![("expr", self.expr(e))]),
            ExprKind::ErrorSuppress(e) => C::N(head("UNARY_OP", 260), vec![("expr", self.expr(e))]),
            ExprKind::Empty(e) => node("EMPTY", vec![("expr", self.expr(e))]),
            ExprKind::Isset(vs) => {
                // `isset($a, $b)` => AST_ISSET nested via AND in Zend; single => ISSET.
                let mut it = vs.iter().rev();
                let last = it.next().expect("isset has >=1 arg");
                let mut acc = node("ISSET", vec![("var", self.expr(last))]);
                for v in it {
                    acc = node("AND", vec![("left", node("ISSET", vec![("var", self.expr(v))])), ("right", acc)]);
                }
                acc
            }
            ExprKind::PreInc(e) => node("PRE_INC", vec![("var", self.expr(e))]),
            ExprKind::PreDec(e) => node("PRE_DEC", vec![("var", self.expr(e))]),
            ExprKind::PostInc(e) => node("POST_INC", vec![("var", self.expr(e))]),
            ExprKind::PostDec(e) => node("POST_DEC", vec![("var", self.expr(e))]),
            ExprKind::Cast { kind, expr } => C::N(head("CAST", cast_code(*kind)), vec![("expr", self.expr(expr))]),
            ExprKind::Instanceof { expr, class } => node("INSTANCEOF", vec![("expr", self.expr(expr)), ("class", self.class_or_name(class))]),
            ExprKind::Interpolated(parts) => C::N("ENCAPS_LIST".into(), parts.iter().map(|p| ("", self.encaps_part(p))).collect()),
            ExprKind::ShellExec(parts) => {
                let encaps = C::N("ENCAPS_LIST".into(), parts.iter().map(|p| ("", self.encaps_part(p))).collect());
                node("SHELL_EXEC", vec![("expr", encaps)])
            }
            ExprKind::Match { subject, arms } => {
                let a: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        let cond = match &arm.conds {
                            Some(cs) => C::N("EXPR_LIST".into(), cs.iter().map(|c| ("", self.expr(c))).collect()),
                            None => C::Null,
                        };
                        ("", node("MATCH_ARM", vec![("cond", cond), ("expr", self.expr(&arm.body))]))
                    })
                    .collect();
                node("MATCH", vec![("cond", self.expr(subject)), ("stmts", C::N("MATCH_ARM_LIST".into(), a))])
            }
            ExprKind::Closure(c) => {
                let flag = if c.is_static { 16 } else { 0 } | if c.by_ref { 4096 } else { 0 } | gen_flag(&c.body);
                let uses = if c.uses.is_empty() {
                    C::Null
                } else {
                    C::N("CLOSURE_USES".into(), c.uses.iter().map(|u| {
                        ("", C::N(head("CLOSURE_VAR", if u.by_ref { 1 } else { 0 }), vec![("name", C::Str(self.sym(u.name)))]))
                    }).collect())
                };
                C::N(
                    head("CLOSURE", flag),
                    vec![
                        ("params", self.params(&c.params)),
                        ("uses", uses),
                        ("stmts", C::N("STMT_LIST".into(), self.stmt_list(&c.body))),
                        ("returnType", self.opt_type(&c.return_type)),
                        ("attributes", self.attrs(&c.attrs)),
                    ],
                )
            }
            ExprKind::ArrowFn(a) => {
                let flag = if a.is_static { 16 } else { 0 } | if a.by_ref { 4096 } else { 0 };
                C::N(
                    head("ARROW_FUNC", flag),
                    vec![
                        ("params", self.params(&a.params)),
                        ("stmts", node("RETURN", vec![("expr", self.expr(&a.body))])),
                        ("returnType", self.opt_type(&a.return_type)),
                        ("attributes", self.attrs(&a.attrs)),
                    ],
                )
            }
            ExprKind::Include { kind, expr } => {
                let f = match kind {
                    IncludeKind::Include => 2,
                    IncludeKind::IncludeOnce => 4,
                    IncludeKind::Require => 8,
                    IncludeKind::RequireOnce => 16,
                };
                C::N(head("INCLUDE_OR_EVAL", f), vec![("expr", self.expr(expr))])
            }
            ExprKind::Eval(e) => C::N(head("INCLUDE_OR_EVAL", 1), vec![("expr", self.expr(e))]),
            // PHP 8.4+: `exit`/`die` with no argument is a plain call to the
            // (unqualified, flag 0) function `exit`; only a parenthesized argument
            // produces an EXIT node.
            ExprKind::Exit(a) => match a {
                Some(arg) => node("EXIT", vec![("expr", self.expr(arg))]),
                None => node(
                    "CALL",
                    vec![
                        ("expr", node("NAME", vec![("name", C::Str("exit".into()))])),
                        ("args", C::N("ARG_LIST".into(), vec![])),
                    ],
                ),
            },
            ExprKind::Yield { key, value } => node(
                "YIELD",
                vec![("value", self.opt(value.as_deref())), ("key", self.opt(key.as_deref()))],
            ),
            ExprKind::YieldFrom(e) => node("YIELD_FROM", vec![("expr", self.expr(e))]),
            ExprKind::Paren(inner) => self.paren(inner),
            ExprKind::Error => C::N("ERROR".into(), vec![]),
            _ => C::N("UNMAPPED_EXPR".into(), vec![]),
        }
    }

    /// A parenthesized expression: transparent, except PHP records it on
    /// conditionals (`#1`), static props (`#1`), and treats a parenthesized name
    /// as a constant fetch.
    fn paren(&self, inner: &Expr) -> C {
        match &inner.kind {
            ExprKind::Ternary { cond, then, els } => C::N(
                head("CONDITIONAL", 1),
                vec![("cond", self.expr(cond)), ("true", self.opt(then.as_deref())), ("false", self.expr(els))],
            ),
            ExprKind::Name(n) => self.const_or_magic(n),
            _ => self.expr(inner),
        }
    }

    /// Render an expression in dereference position (the base of `->`, `[]`, or
    /// the class of `::`). A parenthesized static-prop being dereferenced carries
    /// the PARENTHESIZED_STATIC_PROP flag (#1); a plain call `(A::$b)()` or `new`
    /// does not.
    fn deref(&self, e: &Expr) -> C {
        if let ExprKind::Paren(inner) = &e.kind {
            if let ExprKind::StaticProp { class, name } = &inner.kind {
                let prop = match name {
                    MemberName::Var(s) | MemberName::Ident(s) => C::Str(self.sym(*s)),
                    MemberName::Expr(ex) => self.expr(ex),
                };
                return C::N(head("STATIC_PROP", 1), vec![("class", self.class_or_name(class)), ("prop", prop)]);
            }
        }
        self.expr(e)
    }

    /// Like [`deref`], but for class-name positions (`::`), falling back to
    /// [`class_or_name`] rather than [`expr`].
    fn deref_class(&self, e: &Expr) -> C {
        if let ExprKind::Paren(inner) = &e.kind {
            if matches!(&inner.kind, ExprKind::StaticProp { .. }) {
                return self.deref(e);
            }
        }
        self.class_or_name(e)
    }

    /// A bare name in expression position is a constant fetch — unless it is a
    /// magic constant.
    fn const_or_magic(&self, n: &Name) -> C {
        if n.fq == NameFq::NotFq {
            if let Some(flag) = magic_const_flag(&n.text) {
                return C::N(head("MAGIC_CONST", flag), vec![]);
            }
        }
        node("CONST", vec![("name", self.name_ref(n))])
    }

    /// A name used as a class/function reference is a bare NAME (not CONST).
    fn class_or_name(&self, e: &Expr) -> C {
        match &e.kind {
            ExprKind::Name(n) => self.name_ref(n),
            _ => self.expr(e),
        }
    }

    fn name_ref(&self, n: &Name) -> C {
        let (flag, text) = match n.fq {
            NameFq::Fq => (0, n.text.trim_start_matches('\\').to_string()),
            NameFq::NotFq => (1, n.text.clone()),
            // php-ast strips the leading `namespace\` from relative names.
            NameFq::Relative => {
                (2, n.text.split_once('\\').map(|(_, r)| r).unwrap_or(&n.text).to_string())
            }
        };
        C::N(head("NAME", flag), vec![("name", C::Str(text))])
    }

    fn binary(&self, op: BinOp, lhs: &Expr, rhs: &Expr) -> C {
        // php-ast represents every binary operator as BINARY_OP#flag.
        C::N(head("BINARY_OP", binop_flag(op)), vec![("left", self.expr(lhs)), ("right", self.expr(rhs))])
    }

    fn unary(&self, op: UnOp, e: &Expr) -> C {
        let flag = match op {
            UnOp::BitNot => 13,
            UnOp::Not => 14,
            UnOp::Plus => 261,
            UnOp::Minus => 262,
        };
        C::N(head("UNARY_OP", flag), vec![("expr", self.expr(e))])
    }

    fn member(&self, m: &MemberName) -> C {
        match m {
            MemberName::Ident(s) => C::Str(self.sym(*s)),
            MemberName::Var(s) => node("VAR", vec![("name", C::Str(self.sym(*s)))]),
            MemberName::Expr(e) => self.expr(e),
        }
    }

    fn args(&self, args: &[Arg]) -> C {
        if args.iter().any(|a| a.placeholder) {
            return C::N("CALLABLE_CONVERT".into(), vec![]);
        }
        let kids: Vec<_> = args
            .iter()
            .map(|a| {
                let v = if a.spread {
                    node("UNPACK", vec![("expr", self.expr(&a.value))])
                } else if let Some(name) = a.name {
                    node("NAMED_ARG", vec![("name", C::Str(self.sym(name))), ("expr", self.expr(&a.value))])
                } else {
                    self.expr(&a.value)
                };
                ("", v)
            })
            .collect();
        C::N("ARG_LIST".into(), kids)
    }

    fn array(&self, items: &[ArrayItem], syntax: ArraySyntax) -> C {
        let kids: Vec<_> = items
            .iter()
            .map(|it| {
                let c = match &it.value {
                    None => C::Null,
                    Some(v) if it.spread => node("UNPACK", vec![("expr", self.expr(v))]),
                    Some(v) => C::N(
                        head("ARRAY_ELEM", if it.by_ref { 1 } else { 0 }),
                        vec![("value", self.expr(v)), ("key", it.key.as_ref().map(|k| self.expr(k)).unwrap_or(C::Null))],
                    ),
                };
                ("", c)
            })
            .collect();
        let flag = match syntax {
            ArraySyntax::List => 1,
            ArraySyntax::Long => 2,
            ArraySyntax::Short => 3,
        };
        C::N(head("ARRAY", flag), kids)
    }

    fn encaps_part(&self, p: &Expr) -> C {
        self.expr(p)
    }

    fn expr_list(&self, es: &[Expr]) -> C {
        if es.is_empty() {
            C::Null
        } else {
            C::N("EXPR_LIST".into(), es.iter().map(|e| ("", self.expr(e))).collect())
        }
    }

    // --- types ------------------------------------------------------------

    fn opt_type(&self, t: &Option<Type>) -> C {
        t.as_ref().map(|t| self.ty(t)).unwrap_or(C::Null)
    }

    fn ty(&self, t: &Type) -> C {
        match &t.kind {
            TypeKind::Simple(n) => self.type_name(n),
            TypeKind::Nullable(inner) => node("NULLABLE_TYPE", vec![("type", self.ty(inner))]),
            TypeKind::Union(parts) => C::N("TYPE_UNION".into(), parts.iter().map(|p| ("", self.ty(p))).collect()),
            TypeKind::Intersection(parts) => C::N("TYPE_INTERSECTION".into(), parts.iter().map(|p| ("", self.ty(p))).collect()),
        }
    }

    fn type_name(&self, n: &Name) -> C {
        if n.fq == NameFq::NotFq {
            if let Some(code) = builtin_type_code(&n.text) {
                return C::N(head("TYPE", code), vec![]);
            }
        }
        self.name_ref(n)
    }
}

fn class_flag(c: &ClassDecl) -> u32 {
    let mut f = match c.kind {
        ClassKind::Class => 0,
        ClassKind::Interface => 1,
        ClassKind::Trait => 2,
        ClassKind::Enum => 268435456 | 32,
    };
    if c.name.is_none() {
        f |= 4; // anonymous class
    }
    if c.modifiers.is_abstract {
        f |= 64;
    }
    if c.modifiers.is_final {
        f |= 32;
    }
    if c.modifiers.is_readonly {
        f |= 65536;
    }
    f
}

fn modifiers_flag(m: &Modifiers, default_public: bool) -> u32 {
    let mut f = 0;
    match m.visibility {
        Some(Visibility::Public) => f |= 1,
        Some(Visibility::Protected) => f |= 2,
        Some(Visibility::Private) => f |= 4,
        None if default_public => f |= 1,
        None => {}
    }
    match m.set_visibility {
        Some(Visibility::Public) => f |= 1024,
        Some(Visibility::Protected) => f |= 2048,
        Some(Visibility::Private) => f |= 4096,
        None => {}
    }
    if m.is_static {
        f |= 16;
    }
    if m.is_final {
        f |= 32;
    }
    if m.is_abstract {
        f |= 64;
    }
    if m.is_readonly {
        f |= 128;
    }
    f
}

/// php-ast `ast\flags\BINARY_*` values — note php-ast normalizes `&&`/`||`/`>`/
/// `>=`/`??`/`|>` into `BINARY_OP` with these high-valued flags.
fn binop_flag(op: BinOp) -> u32 {
    use BinOp::*;
    match op {
        Add => 1, Sub => 2, Mul => 3, Div => 4, Mod => 5, Shl => 6, Shr => 7, Concat => 8,
        BitOr => 9, BitAnd => 10, BitXor => 11, Pow => 12, LogicalXor => 15,
        Identical => 16, NotIdentical => 17, Eq => 18, NotEq => 19, Lt => 20, LtEq => 21,
        Spaceship => 170, Gt => 256, GtEq => 257,
        BoolOr | LogicalOr => 258, BoolAnd | LogicalAnd => 259, Coalesce => 260, Pipe => 261,
    }
}

fn cast_code(k: CastKind) -> u32 {
    match k {
        CastKind::Int => 4,
        CastKind::Float => 5,
        CastKind::String => 6,
        CastKind::Array => 7,
        CastKind::Object => 8,
        CastKind::Bool => 18,
        CastKind::Unset => 1,
        CastKind::Void => 14,
    }
}

/// `ZEND_ACC_GENERATOR` (1<<24) if the body contains `yield`/`yield from`
/// (not counting nested function-like scopes).
fn gen_flag(body: &[Stmt]) -> u32 {
    if body.iter().any(stmt_yields) {
        16777216
    } else {
        0
    }
}

fn stmt_yields(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Expr(e) => expr_yields(e),
        StmtKind::Echo(es) => es.iter().any(expr_yields),
        StmtKind::Return(v) => v.as_ref().is_some_and(expr_yields),
        StmtKind::Block(b) => b.iter().any(stmt_yields),
        StmtKind::If { cond, then, elseifs, els } => {
            expr_yields(cond)
                || stmt_yields(then)
                || elseifs.iter().any(|e| expr_yields(&e.cond) || stmt_yields(&e.body))
                || els.as_deref().is_some_and(stmt_yields)
        }
        StmtKind::While { cond, body } | StmtKind::DoWhile { body, cond } => {
            expr_yields(cond) || stmt_yields(body)
        }
        StmtKind::For { init, cond, update, body } => {
            init.iter().chain(cond).chain(update).any(expr_yields) || stmt_yields(body)
        }
        StmtKind::Foreach { subject, key, value, body, .. } => {
            expr_yields(subject)
                || key.as_ref().is_some_and(expr_yields)
                || expr_yields(value)
                || stmt_yields(body)
        }
        StmtKind::Switch { subject, cases } => {
            expr_yields(subject)
                || cases.iter().any(|c| c.test.as_ref().is_some_and(expr_yields) || c.body.iter().any(stmt_yields))
        }
        StmtKind::Try { body, catches, finally } => {
            body.iter().any(stmt_yields)
                || catches.iter().any(|c| c.body.iter().any(stmt_yields))
                || finally.as_ref().is_some_and(|f| f.iter().any(stmt_yields))
        }
        StmtKind::Break(e) | StmtKind::Continue(e) => e.as_ref().is_some_and(expr_yields),
        StmtKind::Global(vs) | StmtKind::Unset(vs) => vs.iter().any(expr_yields),
        StmtKind::StaticVars(vs) => vs.iter().any(|v| v.default.as_ref().is_some_and(expr_yields)),
        // Declarations introduce a new scope (or contain no yields): don't descend.
        _ => false,
    }
}

fn expr_yields(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Yield { .. } | ExprKind::YieldFrom(_) => true,
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::Assign { target: lhs, rhs }
        | ExprKind::AssignRef { target: lhs, rhs }
        | ExprKind::AssignOp { target: lhs, rhs, .. }
        | ExprKind::Coalesce { lhs, rhs } => expr_yields(lhs) || expr_yields(rhs),
        ExprKind::Unary { expr, .. }
        | ExprKind::Cast { expr, .. }
        | ExprKind::Clone(expr)
        | ExprKind::Print(expr)
        | ExprKind::Throw(expr)
        | ExprKind::ErrorSuppress(expr)
        | ExprKind::Empty(expr)
        | ExprKind::PreInc(expr)
        | ExprKind::PreDec(expr)
        | ExprKind::PostInc(expr)
        | ExprKind::PostDec(expr) => expr_yields(expr),
        ExprKind::Ternary { cond, then, els } => {
            expr_yields(cond) || then.as_deref().is_some_and(expr_yields) || expr_yields(els)
        }
        ExprKind::Call { callee, args } => expr_yields(callee) || args.iter().any(|a| expr_yields(&a.value)),
        ExprKind::MethodCall { recv, args, .. } => expr_yields(recv) || args.iter().any(|a| expr_yields(&a.value)),
        ExprKind::StaticCall { class, args, .. } => expr_yields(class) || args.iter().any(|a| expr_yields(&a.value)),
        ExprKind::New { class, args } => expr_yields(class) || args.iter().any(|a| expr_yields(&a.value)),
        ExprKind::Index { base, index } => expr_yields(base) || index.as_deref().is_some_and(expr_yields),
        ExprKind::Prop { base, .. } => expr_yields(base),
        ExprKind::StaticProp { class, .. } => expr_yields(class),
        ExprKind::Instanceof { expr, class } => expr_yields(expr) || expr_yields(class),
        ExprKind::Array { items, .. } => items.iter().any(|it| {
            it.key.as_ref().is_some_and(expr_yields) || it.value.as_ref().is_some_and(expr_yields)
        }),
        ExprKind::Isset(vs) => vs.iter().any(expr_yields),
        ExprKind::Match { subject, arms } => {
            expr_yields(subject)
                || arms.iter().any(|a| {
                    a.conds.as_ref().is_some_and(|cs| cs.iter().any(expr_yields)) || expr_yields(&a.body)
                })
        }
        ExprKind::Interpolated(parts) => parts.iter().any(expr_yields),
        ExprKind::Exit(a) => a.as_deref().is_some_and(expr_yields),
        ExprKind::Include { expr, .. } | ExprKind::Eval(expr) => expr_yields(expr),
        ExprKind::Paren(inner) => expr_yields(inner),
        // Closures / arrow fns / anonymous classes are separate scopes.
        _ => false,
    }
}

fn builtin_type_code(name: &str) -> Option<u32> {
    Some(match name.to_ascii_lowercase().as_str() {
        "null" => 1,
        "false" => 2,
        "true" => 3,
        "int" => 4,
        "float" => 5,
        "string" => 6,
        "array" => 7,
        "object" => 8,
        "callable" => 12,
        "iterable" => 13,
        "void" => 14,
        "static" => 15,
        "mixed" => 16,
        "never" => 17,
        "bool" => 18,
        _ => return None,
    })
}

fn magic_const_flag(name: &str) -> Option<u32> {
    Some(match name.to_ascii_uppercase().as_str() {
        "__LINE__" => 346,
        "__FILE__" => 347,
        "__DIR__" => 348,
        "__CLASS__" => 349,
        "__TRAIT__" => 350,
        "__METHOD__" => 351,
        "__FUNCTION__" => 352,
        "__PROPERTY__" => 353,
        "__NAMESPACE__" => 354,
        _ => return None,
    })
}

