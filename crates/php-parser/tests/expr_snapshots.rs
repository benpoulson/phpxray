//! TDD Tier B: AST snapshots for the expression core. The s-expression renderer
//! makes operator precedence/associativity trivially reviewable.

use php_ast::*;
use php_intern::Interner;

/// Parse a source snippet and render its first statement's expression as an
/// s-expression. Panics on anything but a single expression statement (keeps the
/// matrix focused).
fn sexpr(src: &str) -> String {
    let full = format!("<?php {src};");
    let r = php_parser::parse(&full);
    let stmt = r.program.stmts.first().expect("one statement");
    match &stmt.kind {
        StmtKind::Expr(e) => render(e, &r.interner),
        other => panic!("expected expression statement, got {other:?}"),
    }
}

fn render(e: &Expr, i: &Interner) -> String {
    use ExprKind::*;
    match &e.kind {
        Int(n) => n.to_string(),
        Float(f) => format!("{f:?}"),
        Str(s) => format!("\"{s}\""),
        Interpolated(parts) => {
            let inner: Vec<_> = parts.iter().map(|p| render(p, i)).collect();
            format!("(interp {})", inner.join(" "))
        }
        Variable(s) => format!("${}", i.resolve(*s)),
        VariableVariable(inner) => format!("($$ {})", render(inner, i)),
        Name(n) => n.text.clone(),
        Array(items) => {
            let inner: Vec<_> = items
                .iter()
                .map(|it| {
                    let v = it.value.as_ref().map(|v| render(v, i)).unwrap_or_else(|| "_".into());
                    let v = if it.by_ref { format!("&{v}") } else { v };
                    let v = if it.spread { format!("...{v}") } else { v };
                    match &it.key {
                        Some(k) => format!("{}=>{}", render(k, i), v),
                        None => v,
                    }
                })
                .collect();
            format!("(array {})", inner.join(" "))
        }
        Call { callee, args } => format!("(call {} {})", render(callee, i), render_args(args, i)),
        MethodCall { recv, nullsafe, method, args } => format!(
            "({} {} {} {})",
            if *nullsafe { "?->call" } else { "->call" },
            render(recv, i),
            member(method, i),
            render_args(args, i)
        ),
        StaticCall { class, method, args } => {
            format!("(::call {} {} {})", render(class, i), member(method, i), render_args(args, i))
        }
        New { class, args } => format!("(new {} {})", render(class, i), render_args(args, i)),
        Index { base, index } => {
            let idx = index.as_ref().map(|x| render(x, i)).unwrap_or_default();
            format!("(idx {} {})", render(base, i), idx)
        }
        Prop { base, nullsafe, name } => {
            format!("({} {} {})", if *nullsafe { "?->" } else { "->" }, render(base, i), member(name, i))
        }
        StaticProp { class, name } => format!("(::$ {} {})", render(class, i), member(name, i)),
        ClassConst { class, name } => format!("(:: {} {})", render(class, i), member(name, i)),
        Unary { op, expr } => format!("({} {})", unop(*op), render(expr, i)),
        Binary { op, lhs, rhs } => format!("({} {} {})", binop(*op), render(lhs, i), render(rhs, i)),
        Assign { target, rhs } => format!("(= {} {})", render(target, i), render(rhs, i)),
        AssignOp { op, target, rhs } => {
            format!("({}= {} {})", binop(*op), render(target, i), render(rhs, i))
        }
        AssignRef { target, rhs } => format!("(=& {} {})", render(target, i), render(rhs, i)),
        Cast { kind, expr } => format!("(cast:{kind:?} {})", render(expr, i)),
        Ternary { cond, then, els } => match then {
            Some(t) => format!("(?: {} {} {})", render(cond, i), render(t, i), render(els, i)),
            None => format!("(?: {} {})", render(cond, i), render(els, i)),
        },
        Coalesce { lhs, rhs } => format!("(?? {} {})", render(lhs, i), render(rhs, i)),
        PreInc(e) => format!("(++ {})", render(e, i)),
        PreDec(e) => format!("(-- {})", render(e, i)),
        PostInc(e) => format!("({} ++)", render(e, i)),
        PostDec(e) => format!("({} --)", render(e, i)),
        Instanceof { expr, class } => format!("(instanceof {} {})", render(expr, i), render(class, i)),
        Clone(e) => format!("(clone {})", render(e, i)),
        Print(e) => format!("(print {})", render(e, i)),
        Throw(e) => format!("(throw {})", render(e, i)),
        ErrorSuppress(e) => format!("(@ {})", render(e, i)),
        Yield { key, value } => match (key, value) {
            (None, None) => "(yield)".into(),
            (None, Some(v)) => format!("(yield {})", render(v, i)),
            (Some(k), Some(v)) => format!("(yield {} {})", render(k, i), render(v, i)),
            (Some(_), None) => "(yield ?)".into(),
        },
        YieldFrom(e) => format!("(yield-from {})", render(e, i)),
        Exit(a) => match a {
            Some(a) => format!("(exit {})", render(a, i)),
            None => "(exit)".into(),
        },
        Match { subject, arms } => {
            let arms: Vec<_> = arms
                .iter()
                .map(|a| {
                    let conds = match &a.conds {
                        Some(cs) => cs.iter().map(|c| render(c, i)).collect::<Vec<_>>().join(","),
                        None => "default".into(),
                    };
                    format!("({conds} => {})", render(&a.body, i))
                })
                .collect();
            format!("(match {} {})", render(subject, i), arms.join(" "))
        }
        Include { kind, expr } => format!("({kind:?} {})", render(expr, i)),
        Eval(e) => format!("(eval {})", render(e, i)),
        Isset(vs) => format!("(isset {})", vs.iter().map(|v| render(v, i)).collect::<Vec<_>>().join(" ")),
        Empty(e) => format!("(empty {})", render(e, i)),
        Closure(c) => {
            let st = if c.is_static { "static " } else { "" };
            let uses = if c.uses.is_empty() {
                String::new()
            } else {
                let us: Vec<_> = c
                    .uses
                    .iter()
                    .map(|u| format!("{}{}", if u.by_ref { "&" } else { "" }, i.resolve(u.name)))
                    .collect();
                format!(" use({})", us.join(","))
            };
            format!(
                "({st}closure ({}){}{} [{}])",
                params(&c.params, i),
                uses,
                ret(&c.return_type),
                stmts(&c.body, i)
            )
        }
        ArrowFn(a) => {
            let st = if a.is_static { "static " } else { "" };
            format!("({st}fn ({}){} => {})", params(&a.params, i), ret(&a.return_type), render(&a.body, i))
        }
        NewAnon { class, args } => format!("(new-anon {} {})", render_class(class, i), render_args(args, i)),
        Error => "<error>".into(),
        _ => "<unknown>".into(),
    }
}

fn ty(t: &Type) -> String {
    match &t.kind {
        TypeKind::Simple(n) => n.text.clone(),
        TypeKind::Nullable(inner) => format!("?{}", ty(inner)),
        TypeKind::Union(parts) => parts.iter().map(ty).collect::<Vec<_>>().join("|"),
        TypeKind::Intersection(parts) => {
            format!("({})", parts.iter().map(ty).collect::<Vec<_>>().join("&"))
        }
    }
}

fn ret(t: &Option<Type>) -> String {
    t.as_ref().map(|t| format!(": {}", ty(t))).unwrap_or_default()
}

fn mods(m: &Modifiers) -> String {
    let mut s = Vec::new();
    if let Some(v) = m.visibility {
        s.push(format!("{v:?}").to_lowercase());
    }
    if let Some(v) = m.set_visibility {
        s.push(format!("{}(set)", format!("{v:?}").to_lowercase()));
    }
    if m.is_static {
        s.push("static".into());
    }
    if m.is_abstract {
        s.push("abstract".into());
    }
    if m.is_final {
        s.push("final".into());
    }
    if m.is_readonly {
        s.push("readonly".into());
    }
    s.join(" ")
}

fn params(ps: &[Param], i: &Interner) -> String {
    ps.iter()
        .map(|p| {
            let mut s = String::new();
            let m = mods(&p.modifiers);
            if !m.is_empty() {
                s.push_str(&m);
                s.push(' ');
            }
            if let Some(t) = &p.ty {
                s.push_str(&ty(t));
                s.push(' ');
            }
            if p.by_ref {
                s.push('&');
            }
            if p.variadic {
                s.push_str("...");
            }
            s.push('$');
            s.push_str(i.resolve(p.name));
            if let Some(d) = &p.default {
                s.push_str(&format!("={}", render(d, i)));
            }
            s
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn stmts(ss: &[Stmt], i: &Interner) -> String {
    ss.iter().map(|s| render_stmt(s, i)).collect::<Vec<_>>().join(" ")
}

fn render_class(c: &ClassDecl, i: &Interner) -> String {
    let name = c.name.map(|n| i.resolve(n).to_string()).unwrap_or_else(|| "<anon>".into());
    let m = mods(&c.modifiers);
    let m = if m.is_empty() { String::new() } else { format!("{m} ") };
    let backing = c.backing.as_ref().map(|t| format!(":{}", ty(t))).unwrap_or_default();
    let ext = if c.extends.is_empty() {
        String::new()
    } else {
        format!(" extends {}", c.extends.iter().map(|n| n.text.clone()).collect::<Vec<_>>().join(","))
    };
    let imp = if c.implements.is_empty() {
        String::new()
    } else {
        format!(
            " implements {}",
            c.implements.iter().map(|n| n.text.clone()).collect::<Vec<_>>().join(",")
        )
    };
    let members: Vec<_> = c.members.iter().map(|mem| render_member(mem, i)).collect();
    format!("({m}{:?} {name}{backing}{ext}{imp} [{}])", c.kind, members.join(" "))
}

fn render_member(m: &Member, i: &Interner) -> String {
    match m {
        Member::Method(d) => {
            let md = mods(&d.modifiers);
            let md = if md.is_empty() { String::new() } else { format!("{md} ") };
            let body = match &d.body {
                Some(b) => format!(" [{}]", stmts(b, i)),
                None => " ;".into(),
            };
            format!("(method {md}{} ({}){}{body})", i.resolve(d.name), params(&d.params, i), ret(&d.return_type))
        }
        Member::Property(d) => {
            let md = mods(&d.modifiers);
            let md = if md.is_empty() { String::new() } else { format!("{md} ") };
            let t = d.ty.as_ref().map(|t| format!("{} ", ty(t))).unwrap_or_default();
            let ps: Vec<_> = d
                .props
                .iter()
                .map(|p| match &p.default {
                    Some(v) => format!("${}={}", i.resolve(p.name), render(v, i)),
                    None => format!("${}", i.resolve(p.name)),
                })
                .collect();
            let hook = if d.hooked { " {hooks}" } else { "" };
            format!("(prop {md}{t}{}{hook})", ps.join(" "))
        }
        Member::ClassConst(d) => {
            let md = mods(&d.modifiers);
            let md = if md.is_empty() { String::new() } else { format!("{md} ") };
            let cs: Vec<_> = d.consts.iter().map(|c| format!("{}={}", i.resolve(c.name), render(&c.value, i))).collect();
            format!("(const {md}{})", cs.join(" "))
        }
        Member::EnumCase(d) => match &d.value {
            Some(v) => format!("(case {}={})", i.resolve(d.name), render(v, i)),
            None => format!("(case {})", i.resolve(d.name)),
        },
        Member::TraitUse(d) => {
            let ts: Vec<_> = d.traits.iter().map(|n| n.text.clone()).collect();
            format!("(use-trait {}{})", ts.join(","), if d.has_adaptations { " {..}" } else { "" })
        }
    }
}

fn render_args(args: &[Arg], i: &Interner) -> String {
    let parts: Vec<_> = args
        .iter()
        .map(|a| {
            let v = render(&a.value, i);
            let v = if a.spread { format!("...{v}") } else { v };
            match a.name {
                Some(n) => format!("{}:{}", i.resolve(n), v),
                None => v,
            }
        })
        .collect();
    format!("[{}]", parts.join(" "))
}

fn member(m: &MemberName, i: &Interner) -> String {
    match m {
        MemberName::Ident(s) => i.resolve(*s).to_string(),
        MemberName::Var(s) => format!("${}", i.resolve(*s)),
        MemberName::Expr(e) => format!("{{{}}}", render(e, i)),
    }
}

fn unop(op: UnOp) -> &'static str {
    match op {
        UnOp::Plus => "u+",
        UnOp::Minus => "u-",
        UnOp::Not => "!",
        UnOp::BitNot => "~",
    }
}

fn binop(op: BinOp) -> &'static str {
    use BinOp::*;
    match op {
        Add => "+", Sub => "-", Mul => "*", Div => "/", Mod => "%", Pow => "**",
        Concat => ".", BitOr => "|", BitAnd => "&", BitXor => "^", Shl => "<<", Shr => ">>",
        Eq => "==", NotEq => "!=", Identical => "===", NotIdentical => "!==",
        Lt => "<", LtEq => "<=", Gt => ">", GtEq => ">=", Spaceship => "<=>",
        BoolAnd => "&&", BoolOr => "||", LogicalAnd => "and", LogicalOr => "or",
        LogicalXor => "xor", Pipe => "|>", Coalesce => "??",
    }
}

/// Build a `input => sexpr` table for snapshotting.
fn matrix(cases: &[&str]) -> String {
    cases.iter().map(|c| format!("{c:30} => {}", sexpr(c))).collect::<Vec<_>>().join("\n")
}

#[test]
fn precedence_matrix() {
    insta::assert_snapshot!(matrix(&[
        "1 + 2 * 3",
        "1 * 2 + 3",
        "2 ** 3 ** 2",          // ** right-assoc
        "-2 ** 2",              // ** binds tighter than unary minus
        "1 - 2 - 3",            // left-assoc
        "1 . 2 . 3",
        "1 << 2 + 3",
        "$a = $b = $c",         // assignment right-assoc
        "$a = $b + 1",
        "$a == $b && $c",
        "$a && $b || $c",
        "$a ?? $b ?? $c",       // coalesce right-assoc
        "$a ? $b : $c",
        "$a ? $b : $c ? $d : $e",
        "$a ?: $b",
        "!$a && $b",
        "$a instanceof B && $c",
        "$a + $b <=> $c - $d",
        "$x = $a or $b",        // `or` lower than `=`
        "print $a + 1",
    ]));
}

#[test]
fn postfix_and_access() {
    insta::assert_snapshot!(matrix(&[
        "$a->b->c",
        "$a?->b->c",
        "foo()",
        "$a->m(1, 2)",
        "Foo::BAR",
        "Foo::method($x)",
        "Foo::$prop",
        "Foo::class",
        "$a[0][1]",
        "$obj->arr[1]",
        "new Foo(1)",
        "new $cls",
        "$a++ + ++$b",
        "f(...$xs)",
        "g(name: 1, ...$rest)",
        "-$a->b",
    ]));
}

#[test]
fn literals_and_strings() {
    insta::assert_snapshot!(matrix(&[
        "42",
        "0xFF",
        "0b1010",
        "017",
        "1_000_000",
        "3.14",
        "1.2e3",
        "'single'",
        "\"plain\"",
        "[1, 2 => 'b', &$c, ...$d]",
        "[$k => $v]",
    ]));
}

#[test]
fn statements_snapshot() {
    let src = "<?php\n\
        echo 1, 2;\n\
        $x = foo($y) + 3;\n\
        return $x;\n\
        { $a; $b; }\n\
        ;\n\
        if_marker_not_yet;\n";
    let r = php_parser::parse(src);
    let mut out = String::new();
    for s in &r.program.stmts {
        out.push_str(&render_stmt(s, &r.interner));
        out.push('\n');
    }
    insta::assert_snapshot!(out);
}

/// Parse a full program and render each statement on its own line.
fn prog(src: &str) -> String {
    let r = php_parser::parse(src);
    r.program.stmts.iter().map(|s| render_stmt(s, &r.interner)).collect::<Vec<_>>().join("\n")
}

#[test]
fn control_flow_snapshot() {
    insta::assert_snapshot!(prog("<?php\n\
        if ($a) { foo(); } elseif ($b) bar(); else baz();\n\
        if ($a): echo 1; elseif ($b): echo 2; else: echo 3; endif;\n\
        while ($a) { $i++; }\n\
        while ($a): $i++; endwhile;\n\
        do { $i++; } while ($a);\n\
        for ($i = 0; $i < 10; $i++) loop();\n\
        for (;;) {}\n\
        foreach ($xs as $x) use_it($x);\n\
        foreach ($xs as $k => &$v) {}\n\
        foreach ($xs as [$a, $b]) {}\n\
        switch ($x) { case 1: a(); break; case 2: case 3: b(); default: c(); }\n\
    "));
}

#[test]
fn try_and_jumps_snapshot() {
    insta::assert_snapshot!(prog("<?php\n\
        try { risky(); } catch (\\E1 | E2 $e) { handle($e); } finally { cleanup(); }\n\
        try { x(); } catch (E) {}\n\
        break;\n\
        break 2;\n\
        continue;\n\
        goto target;\n\
        target:\n\
        throw new E('x');\n\
    "));
}

#[test]
fn match_snapshot() {
    insta::assert_snapshot!(prog("<?php\n\
        $r = match ($x) { 1, 2 => 'a', 3 => 'b', default => 'c' };\n\
        $r = match (true) { $x > 0 => 'pos', default => 'np', };\n\
    "));
}

#[test]
fn decls_and_namespaces_snapshot() {
    insta::assert_snapshot!(prog("<?php\n\
        namespace App\\Models;\n\
        use App\\Support\\Str;\n\
        use function App\\helpers\\tap;\n\
        use App\\{A, B as C, function d};\n\
        global $a, $b;\n\
        static $x = 1, $y;\n\
        unset($a, $b['k']);\n\
        declare(strict_types=1);\n\
        $v = include 'f.php';\n\
        require_once __DIR__ . '/x.php';\n\
    "));
}

#[test]
fn function_decls_snapshot() {
    insta::assert_snapshot!(prog("<?php\n\
        /** doc */\n\
        function add(int $a, int $b = 0): int { return $a + $b; }\n\
        function &refgen(&$x, ...$rest) { yield $x; }\n\
        function nullable(?string $s, A|B $u, X&Y $i): void {}\n\
        $f = function ($x) use ($y, &$z): int { return $x; };\n\
        $g = static fn (int $n) => $n * 2;\n\
        const PI = 3.14, E = 2.71;\n\
    "));
}

#[test]
fn class_decls_snapshot() {
    insta::assert_snapshot!(prog("<?php\n\
        abstract class Base extends Root implements I1, I2 {\n\
            public const int MAX = 10;\n\
            protected static ?int $count = 0;\n\
            public readonly string $name;\n\
            private int $a = 1, $b = 2;\n\
            public function __construct(public int $x, private readonly string $y) {}\n\
            abstract public function area(): float;\n\
            final protected function tag(): string { return 'x'; }\n\
            use T1, T2;\n\
        }\n\
        interface Shape extends Drawable { public function draw(): void; }\n\
        trait Greet { public function hi() {} }\n\
        enum Suit: string implements HasColor {\n\
            case Hearts = 'H';\n\
            case Spades = 'S';\n\
            public function color(): string { return 'red'; }\n\
        }\n\
    "));
}

#[test]
fn anon_class_and_promotion_snapshot() {
    insta::assert_snapshot!(prog("<?php\n\
        $o = new class(1) extends Base implements I {\n\
            public function __construct(public int $v) {}\n\
        };\n\
        $p = new Point(1, 2);\n\
        $h = new $cls();\n\
    "));
}

#[test]
fn modern_syntax_snapshot() {
    insta::assert_snapshot!(prog("<?php\n\
        $x = isset($a, $b['k']);\n\
        $y = empty($v);\n\
        $c = clone $a;\n\
        $d = clone($a);\n\
        $e = clone($a, ['p' => 1]);\n\
        $f = strlen(...);\n\
        $g = $obj->method(...);\n\
        $h = new readonly class extends B implements I {};\n\
        $r = readonly();\n\
        enum_func();\n\
    "));
}

fn render_stmt(s: &Stmt, i: &Interner) -> String {
    match &s.kind {
        StmtKind::Expr(e) => format!("(expr {})", render(e, i)),
        StmtKind::Echo(es) => {
            let parts: Vec<_> = es.iter().map(|e| render(e, i)).collect();
            format!("(echo {})", parts.join(" "))
        }
        StmtKind::Return(v) => match v {
            Some(v) => format!("(return {})", render(v, i)),
            None => "(return)".into(),
        },
        StmtKind::Block(b) => {
            let parts: Vec<_> = b.iter().map(|s| render_stmt(s, i)).collect();
            format!("(block {})", parts.join(" "))
        }
        StmtKind::InlineHtml(h) => format!("(html {h:?})"),
        StmtKind::Nop => "(nop)".into(),
        StmtKind::Error => "(error)".into(),
        StmtKind::If { cond, then, elseifs, els } => {
            let mut s = format!("(if {} {}", render(cond, i), render_stmt(then, i));
            for ei in elseifs {
                s.push_str(&format!(" (elseif {} {})", render(&ei.cond, i), render_stmt(&ei.body, i)));
            }
            if let Some(e) = els {
                s.push_str(&format!(" (else {})", render_stmt(e, i)));
            }
            s.push(')');
            s
        }
        StmtKind::While { cond, body } => format!("(while {} {})", render(cond, i), render_stmt(body, i)),
        StmtKind::DoWhile { body, cond } => {
            format!("(do-while {} {})", render_stmt(body, i), render(cond, i))
        }
        StmtKind::For { init, cond, update, body } => format!(
            "(for [{}] [{}] [{}] {})",
            exprs(init, i),
            exprs(cond, i),
            exprs(update, i),
            render_stmt(body, i)
        ),
        StmtKind::Foreach { subject, key, value, by_ref, body } => {
            let v = if *by_ref { format!("&{}", render(value, i)) } else { render(value, i) };
            let kv = match key {
                Some(k) => format!("{} => {v}", render(k, i)),
                None => v,
            };
            format!("(foreach {} as {kv} {})", render(subject, i), render_stmt(body, i))
        }
        StmtKind::Switch { subject, cases } => {
            let cs: Vec<_> = cases
                .iter()
                .map(|c| {
                    let t = c.test.as_ref().map(|e| render(e, i)).unwrap_or_else(|| "default".into());
                    let body: Vec<_> = c.body.iter().map(|s| render_stmt(s, i)).collect();
                    format!("(case {t} {})", body.join(" "))
                })
                .collect();
            format!("(switch {} {})", render(subject, i), cs.join(" "))
        }
        StmtKind::Try { body, catches, finally } => {
            let b: Vec<_> = body.iter().map(|s| render_stmt(s, i)).collect();
            let mut s = format!("(try [{}]", b.join(" "));
            for c in catches {
                let types: Vec<_> = c.types.iter().map(|t| t.text.clone()).collect();
                let var = c.var.map(|v| format!(" ${}", i.resolve(v))).unwrap_or_default();
                let cb: Vec<_> = c.body.iter().map(|s| render_stmt(s, i)).collect();
                s.push_str(&format!(" (catch {}{var} [{}])", types.join("|"), cb.join(" ")));
            }
            if let Some(f) = finally {
                let fb: Vec<_> = f.iter().map(|s| render_stmt(s, i)).collect();
                s.push_str(&format!(" (finally [{}])", fb.join(" ")));
            }
            s.push(')');
            s
        }
        StmtKind::Break(l) => with_opt("break", l.as_ref(), i),
        StmtKind::Continue(l) => with_opt("continue", l.as_ref(), i),
        StmtKind::Goto(s) => format!("(goto {})", i.resolve(*s)),
        StmtKind::Label(s) => format!("(label {})", i.resolve(*s)),
        StmtKind::Global(vs) => format!("(global {})", exprs(vs, i)),
        StmtKind::StaticVars(vs) => {
            let parts: Vec<_> = vs
                .iter()
                .map(|v| match &v.default {
                    Some(d) => format!("${}={}", i.resolve(v.name), render(d, i)),
                    None => format!("${}", i.resolve(v.name)),
                })
                .collect();
            format!("(static {})", parts.join(" "))
        }
        StmtKind::Unset(vs) => format!("(unset {})", exprs(vs, i)),
        StmtKind::Declare { directives, body } => {
            let ds: Vec<_> = directives
                .iter()
                .map(|(n, e)| format!("{}={}", i.resolve(*n), render(e, i)))
                .collect();
            match body {
                Some(b) => format!("(declare [{}] {})", ds.join(" "), render_stmt(b, i)),
                None => format!("(declare [{}])", ds.join(" ")),
            }
        }
        StmtKind::Namespace { name, body } => {
            let n = name.as_ref().map(|n| n.text.clone()).unwrap_or_default();
            match body {
                Some(b) => {
                    let bs: Vec<_> = b.iter().map(|s| render_stmt(s, i)).collect();
                    format!("(namespace {n} [{}])", bs.join(" "))
                }
                None => format!("(namespace {n})"),
            }
        }
        StmtKind::Use(items) => {
            let parts: Vec<_> = items
                .iter()
                .map(|u| {
                    let a = u.alias.map(|a| format!(" as {}", i.resolve(a))).unwrap_or_default();
                    format!("{:?}:{}{a}", u.kind, u.name.text)
                })
                .collect();
            format!("(use {})", parts.join(" "))
        }
        StmtKind::Function(f) => {
            let r = if f.by_ref { "&" } else { "" };
            let doc = f.doc.as_deref().map(|d| format!("{d:?} ")).unwrap_or_default();
            format!(
                "{doc}(function {r}{} ({}){} [{}])",
                i.resolve(f.name),
                params(&f.params, i),
                ret(&f.return_type),
                stmts(&f.body, i)
            )
        }
        StmtKind::Class(c) => {
            let doc = c.doc.as_deref().map(|d| format!("{d:?} ")).unwrap_or_default();
            format!("{doc}{}", render_class(c, i))
        }
        StmtKind::ConstDecl(elems) => {
            let cs: Vec<_> = elems.iter().map(|c| format!("{}={}", i.resolve(c.name), render(&c.value, i))).collect();
            format!("(const {})", cs.join(" "))
        }
        _ => "(unknown)".into(),
    }
}

fn exprs(es: &[Expr], i: &Interner) -> String {
    es.iter().map(|e| render(e, i)).collect::<Vec<_>>().join(" ")
}

fn with_opt(name: &str, e: Option<&Expr>, i: &Interner) -> String {
    match e {
        Some(e) => format!("({name} {})", render(e, i)),
        None => format!("({name})"),
    }
}
