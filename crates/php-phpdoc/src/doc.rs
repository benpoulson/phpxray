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
    pub deprecated: bool,
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
    let mut doc = Doc { description: block.description, ..Doc::default() };
    // Param/return precedence: track the priority that set each.
    let mut return_pri: i8 = -1;
    let mut param_pri: Vec<i8> = Vec::new();

    for tag in &block.tags {
        let (base, pri) = normalize(&tag.name);
        match base {
            "param" => upsert_param(&mut doc.params, &mut param_pri, parse_param(&tag.value), pri),
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
            "deprecated" => doc.deprecated = true,
            _ => {}
        }
    }
    doc
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
    Param { name, ty, by_ref, variadic, description: description.to_string() }
}

fn parse_var(value: &str) -> Var {
    let (ty, rest) = split_type(value);
    let (name, description) = take_var_name(rest);
    Var { name, ty, description: description.to_string() }
}

fn parse_template(value: &str) -> Option<Template> {
    let value = value.trim();
    let end = value.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(value.len());
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
        let end = after.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(after.len());
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
        let d = parse("/**\n * @param int $count how many\n * @param string[] $names\n * @return Thing\n */");
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
            Some(Generic { base: "non-empty-list".into(), args: vec![named("User")] })
        );
        // psalm-return overrides the plain `array`.
        assert_eq!(d.returns, Some(Generic { base: "list".into(), args: vec![named("User")] }));
    }

    #[test]
    fn var_throws_template_deprecated() {
        let d = parse(
            "/**\n * @var array<string, int> $map\n * @throws \\RuntimeException\n * @template T of Countable\n * @deprecated use Other\n */",
        );
        assert_eq!(d.vars[0].ty, Some(Generic { base: "array".into(), args: vec![named("string"), named("int")] }));
        assert_eq!(d.vars[0].name.as_deref(), Some("map"));
        assert_eq!(d.throws, [named("\\RuntimeException")]);
        assert_eq!(d.templates, [Template { name: "T".into(), bound: Some(named("Countable")) }]);
        assert!(d.deprecated);
    }

    #[test]
    fn bare_template_has_no_bound() {
        let d = parse("/** @template TKey */");
        assert_eq!(d.templates, [Template { name: "TKey".into(), bound: None }]);
    }
}
