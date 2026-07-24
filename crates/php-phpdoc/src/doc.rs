//! M-D2: combine the tag layer (M-D0) and the type grammar (M-D1) into a typed
//! [`Doc`] — `@param`/`@return`/`@var`/`@throws`/`@template` with their type
//! operands parsed.
//!
//! `@phpstan-*` and `@psalm-*` variants are treated as the base tag but take
//! precedence over the plain form (phpstan > psalm > standard), since they exist
//! precisely to give a more precise type than the native/plain annotation.

use crate::parse_block;
use crate::types::{parse_type, parse_type_prefix, DocType};

/// A docblock with its type-bearing tags parsed.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Doc {
    pub description: String,
    pub params: Vec<Param>,
    pub returns: Option<DocType>,
    pub vars: Vec<Var>,
    pub throws: Vec<DocType>,
    pub templates: Vec<Template>,
    /// `@method` magic-method declarations (heavily used by Laravel facades /
    /// barryvdh/ide-helper).
    pub methods: Vec<MethodTag>,
    /// `@property`/`@property-read`/`@property-write` magic properties.
    pub properties: Vec<PropertyTag>,
    /// `@mixin` — classes whose members are mixed in.
    pub mixins: Vec<DocType>,
    /// Generic parent type arguments: `@extends`/`@template-extends`.
    pub extends: Vec<DocType>,
    /// Generic interface type arguments: `@implements`/`@template-implements`.
    pub implements: Vec<DocType>,
    /// Generic trait type arguments: `@use`/`@template-use`.
    pub uses: Vec<DocType>,
    /// `@phpstan-assert`/`-if-true`/`-if-false` (and psalm equivalents).
    pub asserts: Vec<AssertTag>,
    /// `@param-out Type $name` — the type a by-ref parameter holds *after*
    /// the call returns.
    pub param_outs: Vec<Param>,
    /// `@phpstan-self-out Type` (`@phpstan-this-out`) — the type `$this` (the
    /// receiver) holds *after* the method returns, for fluent APIs that mutate
    /// the receiver's generic type.
    pub self_out: Option<DocType>,
    pub deprecated: bool,
}

/// A `@phpstan-assert [!]Type $param` assertion: after a call (or in the
/// branch selected by `when`), `$param` is (not) of `Type`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssertTag {
    pub ty: DocType,
    /// The asserted target without the `$`: a parameter name (`value`) or a
    /// `$this` property path (`this->prop`).
    pub param: String,
    /// `!Type` — the value is asserted *not* to be of the type.
    pub negated: bool,
    pub when: AssertWhen,
}

/// Which outcome activates an assertion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssertWhen {
    /// `@phpstan-assert` — holds after the call returns at all.
    Always,
    /// `@phpstan-assert-if-true` — holds when the call returned truthy.
    IfTrue,
    /// `@phpstan-assert-if-false` — holds when the call returned falsy.
    IfFalse,
}

/// A `@method [static] [ret] name(params) [desc]` declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodTag {
    pub name: String,
    pub is_static: bool,
    pub return_type: Option<DocType>,
    pub params: Vec<MethodParam>,
    pub description: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodParam {
    pub name: Option<String>,
    pub ty: Option<DocType>,
    pub by_ref: bool,
    pub variadic: bool,
    /// The default-value text as written (e.g. `[]`, `'x'`), if any.
    pub default: Option<String>,
}

/// A `@property*` magic property.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropertyTag {
    pub name: Option<String>,
    pub ty: Option<DocType>,
    pub access: PropertyAccess,
    pub description: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyAccess {
    ReadWrite,
    ReadOnly,
    WriteOnly,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    /// The parameter variable name without `$` (e.g. `count`); `None` if absent.
    pub name: Option<String>,
    pub ty: Option<DocType>,
    pub by_ref: bool,
    pub variadic: bool,
    pub description: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Var {
    pub name: Option<String>,
    pub ty: Option<DocType>,
    pub description: String,
}

/// `@template T` / `@template T of Bound`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Template {
    pub name: String,
    pub bound: Option<DocType>,
}

/// Parse a raw `/** … */` docblock into a typed [`Doc`].
pub fn parse(raw: &str) -> Doc {
    let block = parse_block(raw);
    let mut doc = Doc {
        description: block.description,
        ..Doc::default()
    };
    // Param/return precedence: track the priority that set each.
    let mut return_pri: i8 = -1;
    let mut param_pri: Vec<i8> = Vec::new();

    for tag in &block.tags {
        let (base, pri) = normalize(&tag.name);
        // `@template-extends` etc. share handling with the bare generic tags.
        let gbase = base.strip_prefix("template-").unwrap_or(base);
        match base {
            "param" => upsert_param(
                &mut doc.params,
                &mut param_pri,
                parse_param(&tag.value),
                pri,
            ),
            "return" => {
                if pri >= return_pri {
                    let (ty, _) = split_type(&tag.value);
                    if ty.is_some() {
                        doc.returns = ty;
                        return_pri = pri;
                    }
                }
            }
            "var" => doc.vars.push(parse_var(&tag.value)),
            "param-out" => doc.param_outs.push(parse_param(&tag.value)),
            // `@phpstan-self-out`/`-this-out` carry type effect only in their
            // prefixed forms (a bare `@self-out` is not a standard tag).
            "self-out" | "this-out" if pri > 0 => {
                if doc.self_out.is_none() {
                    if let Some((ty, _)) = parse_type_prefix(&tag.value) {
                        doc.self_out = Some(ty);
                    }
                }
            }
            "throws" => {
                if let Some((ty, _)) = parse_type_prefix(&tag.value) {
                    doc.throws.push(ty);
                }
            }
            "template" => {
                if let Some(t) = parse_template(&tag.value) {
                    doc.templates.push(t);
                }
            }
            "method" => {
                if let Some(m) = parse_method(&tag.value) {
                    doc.methods.push(m);
                }
            }
            "property" => doc
                .properties
                .push(parse_property(&tag.value, PropertyAccess::ReadWrite)),
            "property-read" => doc
                .properties
                .push(parse_property(&tag.value, PropertyAccess::ReadOnly)),
            "property-write" => doc
                .properties
                .push(parse_property(&tag.value, PropertyAccess::WriteOnly)),
            "mixin" => {
                if let Some((ty, _)) = parse_type_prefix(&tag.value) {
                    doc.mixins.push(ty);
                }
            }
            "deprecated" => doc.deprecated = true,
            // Assertion tags carry type effect only in their prefixed
            // (phpstan-/psalm-) forms; a bare `@assert` is phpDocumentor prose.
            "assert" | "assert-if-true" | "assert-if-false" if pri > 0 => {
                let when = match base {
                    "assert-if-true" => AssertWhen::IfTrue,
                    "assert-if-false" => AssertWhen::IfFalse,
                    _ => AssertWhen::Always,
                };
                if let Some(a) = parse_assert(&tag.value, when) {
                    doc.asserts.push(a);
                }
            }
            // Generic parent/interface/trait type args (incl. `template-` forms).
            _ => match gbase {
                "extends" => push_type(&mut doc.extends, &tag.value),
                "implements" => push_type(&mut doc.implements, &tag.value),
                "use" => push_type(&mut doc.uses, &tag.value),
                _ => {}
            },
        }
    }
    doc
}

/// Parse `[!][=]Type $param` (the `=` "same value" refinement is treated as a
/// plain type assertion). The target is `$name` or a `$this->prop` path.
fn parse_assert(value: &str, when: AssertWhen) -> Option<AssertTag> {
    let mut rest = value.trim_start();
    let negated = rest.starts_with('!');
    if negated {
        rest = rest[1..].trim_start();
    }
    if let Some(stripped) = rest.strip_prefix('=') {
        rest = stripped.trim_start();
    }
    let (ty, n) = crate::parse_type_prefix(rest)?;
    let after = rest[n..].trim_start();
    let target = after.strip_prefix('$')?;
    let end = target
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '>'))
        .unwrap_or(target.len());
    let param = &target[..end];
    if param.is_empty() {
        return None;
    }
    Some(AssertTag {
        ty,
        param: param.to_string(),
        negated,
        when,
    })
}

fn push_type(out: &mut Vec<DocType>, value: &str) {
    if let Some((ty, _)) = parse_type_prefix(value) {
        out.push(ty);
    }
}

/// Strip a `phpstan-`/`psalm-` prefix and return the base tag + its precedence
/// (phpstan = 2, psalm = 1, plain = 0).
fn normalize(name: &str) -> (&str, i8) {
    if let Some(rest) = name.strip_prefix("phpstan-") {
        (rest, 2)
    } else if let Some(rest) = name.strip_prefix("psalm-") {
        (rest, 1)
    } else {
        (name, 0)
    }
}

/// Parse a leading type from `s`, returning it and the remaining text. When `s`
/// starts with `$` there is no type (the variable comes first).
fn split_type(s: &str) -> (Option<DocType>, &str) {
    let t = s.trim_start();
    if t.starts_with('$') {
        return (None, t);
    }
    match parse_type_prefix(t) {
        Some((ty, n)) => (Some(ty), t[n..].trim_start()),
        None => (None, t),
    }
}

fn parse_param(value: &str) -> Param {
    let (ty, mut rest) = split_type(value);
    let by_ref = rest.starts_with('&');
    if by_ref {
        rest = rest[1..].trim_start();
    }
    let variadic = rest.starts_with("...");
    if variadic {
        rest = rest[3..].trim_start();
    }
    let (name, description) = take_var_name(rest);
    Param {
        name,
        ty,
        by_ref,
        variadic,
        description: description.to_string(),
    }
}

fn parse_var(value: &str) -> Var {
    let (ty, rest) = split_type(value);
    let (name, description) = take_var_name(rest);
    Var {
        name,
        ty,
        description: description.to_string(),
    }
}

fn parse_property(value: &str, access: PropertyAccess) -> PropertyTag {
    let (ty, rest) = split_type(value);
    let (name, description) = take_var_name(rest);
    PropertyTag {
        name,
        ty,
        access,
        description: description.to_string(),
    }
}

/// Parse a `@method [static] [returnType] name(params) [description]` signature.
fn parse_method(value: &str) -> Option<MethodTag> {
    let mut v = value.trim();
    let mut is_static = false;
    if let Some(rest) = v.strip_prefix("static") {
        if rest.starts_with(char::is_whitespace) {
            is_static = true;
            v = rest.trim_start();
        }
    }
    let open = v.find('(')?;
    let close = matching_paren(v, open)?;
    // `[returnType] name` precedes the parameter list; the name is the trailing
    // identifier, the return type (if any) is everything before it.
    let head = v[..open].trim_end();
    let name_start = head
        .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .map(|i| i + 1)
        .unwrap_or(0);
    let name = head[name_start..].to_string();
    if name.is_empty() {
        return None;
    }
    let ret_str = head[..name_start].trim();
    let return_type = if ret_str.is_empty() {
        None
    } else {
        parse_type(ret_str)
    };
    let params = split_top_level(&v[open + 1..close], b',')
        .iter()
        .map(|p| parse_method_param(p))
        .collect();
    let description = v[close + 1..].trim().to_string();
    Some(MethodTag {
        name,
        is_static,
        return_type,
        params,
        description,
    })
}

fn parse_method_param(s: &str) -> MethodParam {
    let (decl, default) = match top_level_eq(s) {
        Some(i) => (s[..i].trim(), Some(s[i + 1..].trim().to_string())),
        None => (s.trim(), None),
    };
    let (ty, mut rest) = split_type(decl);
    let by_ref = rest.starts_with('&');
    if by_ref {
        rest = rest[1..].trim_start();
    }
    let variadic = rest.starts_with("...");
    if variadic {
        rest = rest[3..].trim_start();
    }
    let (name, _) = take_var_name(rest);
    MethodParam {
        name,
        ty,
        by_ref,
        variadic,
        default,
    }
}

/// Find the matching close of the bracket at `open` (`()`/`[]`/`{}` nesting;
/// angle brackets are ignored so `=>` in defaults doesn't confuse it).
fn matching_paren(s: &str, open: usize) -> Option<usize> {
    let b = s.as_bytes();
    let mut depth = 0i32;
    for (i, &c) in b.iter().enumerate().skip(open) {
        match c {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Split on `sep` at the top level, respecting `()[]{}` and `<>` nesting.
fn split_top_level(s: &str, sep: u8) -> Vec<&str> {
    let b = s.as_bytes();
    let (mut round, mut angle, mut start) = (0i32, 0i32, 0usize);
    let mut out = Vec::new();
    for (i, &c) in b.iter().enumerate() {
        match c {
            b'(' | b'[' | b'{' => round += 1,
            b')' | b']' | b'}' => round -= 1,
            b'<' => angle += 1,
            b'>' if angle > 0 => angle -= 1,
            _ if c == sep && round == 0 && angle == 0 => {
                out.push(s[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(s[start..].trim());
    out.into_iter().filter(|p| !p.is_empty()).collect()
}

/// The index of the top-level `=` (parameter default assignment), if any.
fn top_level_eq(s: &str) -> Option<usize> {
    let b = s.as_bytes();
    let (mut round, mut angle) = (0i32, 0i32);
    for (i, &c) in b.iter().enumerate() {
        match c {
            b'(' | b'[' | b'{' => round += 1,
            b')' | b']' | b'}' => round -= 1,
            b'<' => angle += 1,
            b'>' if angle > 0 => angle -= 1,
            b'=' if round == 0 && angle == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

fn parse_template(value: &str) -> Option<Template> {
    let value = value.trim();
    let end = value
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(value.len());
    let name = value[..end].to_string();
    if name.is_empty() {
        return None;
    }
    // Optional `of Bound` / `as Bound`.
    let rest = value[end..].trim_start();
    let bound = rest
        .strip_prefix("of ")
        .or_else(|| rest.strip_prefix("as "))
        .and_then(|b| parse_type(b.trim()));
    Some(Template { name, bound })
}

/// If `s` starts with `$name`, split off the name (without `$`) and return the
/// rest as the description.
fn take_var_name(s: &str) -> (Option<String>, &str) {
    let s = s.trim_start();
    if let Some(after) = s.strip_prefix('$') {
        let end = after
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(after.len());
        let name = after[..end].to_string();
        return (Some(name), after[end..].trim_start());
    }
    (None, s)
}

/// Insert or replace a param, keyed by name, keeping the highest-priority source.
/// Unnamed params are always appended.
fn upsert_param(params: &mut Vec<Param>, pris: &mut Vec<i8>, new: Param, pri: i8) {
    if let Some(name) = &new.name {
        if let Some(i) = params.iter().position(|p| p.name.as_deref() == Some(name)) {
            if pri >= pris[i] {
                params[i] = new;
                pris[i] = pri;
            }
            return;
        }
    }
    params.push(new);
    pris.push(pri);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::DocType::*;

    fn named(n: &str) -> DocType {
        Named(n.to_string())
    }

    #[test]
    fn params_and_return() {
        let d = parse(
            "/**\n * @param int $count how many\n * @param string[] $names\n * @return Thing\n */",
        );
        assert_eq!(d.params.len(), 2);
        assert_eq!(d.params[0].name.as_deref(), Some("count"));
        assert_eq!(d.params[0].ty, Some(named("int")));
        assert_eq!(d.params[0].description, "how many");
        assert_eq!(d.params[1].ty, Some(Array(Box::new(named("string")))));
        assert_eq!(d.returns, Some(named("Thing")));
    }

    #[test]
    fn variadic_and_by_ref_params() {
        let d = parse("/**\n * @param int ...$ids\n * @param array &$out\n */");
        assert!(d.params[0].variadic && d.params[0].name.as_deref() == Some("ids"));
        assert!(d.params[1].by_ref && d.params[1].name.as_deref() == Some("out"));
    }

    #[test]
    fn param_without_type_keeps_name() {
        let d = parse("/** @param $thing a thing */");
        assert_eq!(d.params[0].ty, None);
        assert_eq!(d.params[0].name.as_deref(), Some("thing"));
        assert_eq!(d.params[0].description, "a thing");
    }

    #[test]
    fn phpstan_prefix_overrides_plain_param_and_return() {
        let d = parse(
            "/**\n * @param array $items\n * @phpstan-param non-empty-list<User> $items\n * @return array\n * @psalm-return list<User>\n */",
        );
        // The phpstan-param wins for $items.
        assert_eq!(
            d.params[0].ty,
            Some(Generic {
                base: "non-empty-list".into(),
                args: vec![named("User")]
            })
        );
        // psalm-return overrides the plain `array`.
        assert_eq!(
            d.returns,
            Some(Generic {
                base: "list".into(),
                args: vec![named("User")]
            })
        );
    }

    #[test]
    fn var_throws_template_deprecated() {
        let d = parse(
            "/**\n * @var array<string, int> $map\n * @throws \\RuntimeException\n * @template T of Countable\n * @deprecated use Other\n */",
        );
        assert_eq!(
            d.vars[0].ty,
            Some(Generic {
                base: "array".into(),
                args: vec![named("string"), named("int")]
            })
        );
        assert_eq!(d.vars[0].name.as_deref(), Some("map"));
        assert_eq!(d.throws, [named("\\RuntimeException")]);
        assert_eq!(
            d.templates,
            [Template {
                name: "T".into(),
                bound: Some(named("Countable"))
            }]
        );
        assert!(d.deprecated);
    }

    #[test]
    fn bare_template_has_no_bound() {
        let d = parse("/** @template TKey */");
        assert_eq!(
            d.templates,
            [Template {
                name: "TKey".into(),
                bound: None
            }]
        );
    }

    #[test]
    fn method_with_static_return_and_params() {
        let d = parse(
            "/** @method static \\Builder where(string $column, mixed $value = null) finds rows */",
        );
        let m = &d.methods[0];
        assert_eq!(m.name, "where");
        assert!(m.is_static);
        assert_eq!(m.return_type, Some(named("\\Builder")));
        assert_eq!(m.description, "finds rows");
        assert_eq!(m.params.len(), 2);
        assert_eq!(m.params[0].name.as_deref(), Some("column"));
        assert_eq!(m.params[0].ty, Some(named("string")));
        assert_eq!(m.params[1].name.as_deref(), Some("value"));
        assert_eq!(m.params[1].default.as_deref(), Some("null"));
    }

    #[test]
    fn method_without_return_type() {
        let d = parse("/** @method void boot() */");
        assert_eq!(d.methods[0].name, "boot");
        assert_eq!(d.methods[0].return_type, Some(named("void")));
        let d2 = parse("/** @method doThing(int $n) */");
        assert_eq!(d2.methods[0].name, "doThing");
        assert_eq!(d2.methods[0].return_type, None);
    }

    #[test]
    fn method_params_with_generics_variadic_and_array_default() {
        let d = parse(
            "/** @method int sum(array<int, int> $nums, int ...$rest, array $opts = ['a' => 1]) */",
        );
        let m = &d.methods[0];
        assert_eq!(m.params.len(), 3);
        assert_eq!(
            m.params[0].ty,
            Some(Generic {
                base: "array".into(),
                args: vec![named("int"), named("int")]
            })
        );
        assert!(m.params[1].variadic && m.params[1].name.as_deref() == Some("rest"));
        // The `=>` inside the array default must not split the param or default.
        assert_eq!(m.params[2].default.as_deref(), Some("['a' => 1]"));
    }

    #[test]
    fn properties_by_access() {
        let d = parse(
            "/**\n * @property int $id\n * @property-read string $name the name\n * @property-write mixed $value\n */",
        );
        assert_eq!(d.properties.len(), 3);
        assert_eq!(d.properties[0].access, PropertyAccess::ReadWrite);
        assert_eq!(d.properties[0].name.as_deref(), Some("id"));
        assert_eq!(d.properties[0].ty, Some(named("int")));
        assert_eq!(d.properties[1].access, PropertyAccess::ReadOnly);
        assert_eq!(d.properties[1].description, "the name");
        assert_eq!(d.properties[2].access, PropertyAccess::WriteOnly);
    }

    #[test]
    fn assert_tags() {
        let d = parse(
            "/**\n * @phpstan-assert string $value\n * @phpstan-assert-if-true !null $x\n * @psalm-assert-if-false =int $n\n * @phpstan-assert !null $this->conn\n * @assert prose-only tag ignored\n */",
        );
        assert_eq!(d.asserts.len(), 4);
        assert_eq!(d.asserts[0].param, "value");
        assert_eq!(d.asserts[0].ty, named("string"));
        assert!(!d.asserts[0].negated);
        assert_eq!(d.asserts[0].when, AssertWhen::Always);
        assert_eq!(d.asserts[1].param, "x");
        assert!(d.asserts[1].negated);
        assert_eq!(d.asserts[1].when, AssertWhen::IfTrue);
        // `=` (same-value) parses as a plain assertion; psalm prefix accepted.
        assert_eq!(d.asserts[2].param, "n");
        assert_eq!(d.asserts[2].when, AssertWhen::IfFalse);
        // `$this->prop` paths keep the arrow path.
        assert_eq!(d.asserts[3].param, "this->conn");
    }

    #[test]
    fn mixin_and_generic_parents() {
        let d = parse(
            "/**\n * @mixin \\Eloquent\n * @extends Collection<int, User>\n * @implements ArrayAccess<int, User>\n * @template-use HasEvents<User>\n */",
        );
        assert_eq!(d.mixins, [named("\\Eloquent")]);
        assert_eq!(
            d.extends,
            [Generic {
                base: "Collection".into(),
                args: vec![named("int"), named("User")]
            }]
        );
        assert_eq!(
            d.implements,
            [Generic {
                base: "ArrayAccess".into(),
                args: vec![named("int"), named("User")]
            }]
        );
        assert_eq!(
            d.uses,
            [Generic {
                base: "HasEvents".into(),
                args: vec![named("User")]
            }]
        );
    }
}
