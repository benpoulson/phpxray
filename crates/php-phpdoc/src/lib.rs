//! A PHPDoc sub-parser: turns the raw `/** … */` text captured on declarations
//! into structured tags and (later) parsed type expressions.
//!
//! PHPDoc carries the rich type information a static analyzer needs — generics,
//! array shapes, literal types, etc. — in a mini-language that is *not* PHP, so
//! it gets its own parser. This module is layered:
//!
//! - **M-D0 (here):** the *tag splitter* — strip the `/** */` framing and the
//!   per-line `*`, separate the leading description from `@tag` blocks, and join
//!   each tag's (possibly multi-line) body. Description prose is kept opaque, so
//!   `<p>`/`{…}` inside it never confuses anything.
//! - **M-D1:** the type-expression grammar (`DocType`).
//! - **M-D2:** parse each tag's operand into types → a typed `DocBlock`.

mod doc;
mod types;
pub use doc::{
    parse, Doc, MethodParam, MethodTag, Param, PropertyAccess, PropertyTag, Template, Var,
};
pub use types::{parse_type, parse_type_prefix, DocType, ShapeField};

/// A parsed docblock: its leading description and its block tags, in order.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DocBlock {
    /// The free-text summary/description before the first `@tag` (trimmed).
    pub description: String,
    pub tags: Vec<DocTag>,
}

/// One `@tag` and its raw body (type + variable + description, unparsed at this
/// layer). The body joins continuation lines with single spaces, so a type that
/// wraps across lines still reads as one string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocTag {
    /// The tag name without the leading `@` — e.g. `param`, `return`,
    /// `phpstan-return`, `psalm-param`.
    pub name: String,
    /// Everything after the tag name, trimmed; continuation lines space-joined.
    pub value: String,
}

/// Split a raw `/** … */` docblock into its description and block tags.
pub fn parse_block(raw: &str) -> DocBlock {
    let body = strip_frame(raw);
    let mut description: Vec<&str> = Vec::new();
    let mut tags: Vec<DocTag> = Vec::new();

    for line in body.lines() {
        let line = strip_star(line);
        let trimmed = line.trim_start();
        // A block tag starts a line with `@name`. (`{@inline}` tags stay in
        // prose — they don't start the line with a bare `@`.)
        if let Some(rest) = trimmed.strip_prefix('@') {
            if starts_tag(rest) {
                let (name, value) = split_tag(rest);
                tags.push(DocTag { name, value });
                continue;
            }
        }
        match tags.last_mut() {
            // Once tags begin, non-tag lines continue the current tag's body.
            Some(tag) => {
                let t = trimmed.trim_end();
                if !t.is_empty() {
                    if !tag.value.is_empty() {
                        tag.value.push(' ');
                    }
                    tag.value.push_str(t);
                }
            }
            None => description.push(line),
        }
    }

    DocBlock {
        description: description.join("\n").trim().to_string(),
        tags,
    }
}

/// Strip the `/** … */` (or `/* … */`) framing.
fn strip_frame(s: &str) -> &str {
    let s = s.trim();
    let s = s
        .strip_prefix("/**")
        .or_else(|| s.strip_prefix("/*"))
        .unwrap_or(s);
    s.strip_suffix("*/").unwrap_or(s)
}

/// Strip a line's leading whitespace + one decorative `*` (and a following
/// space), as in the conventional `* …` doc layout.
fn strip_star(line: &str) -> &str {
    let t = line.trim_start();
    match t.strip_prefix('*') {
        Some(rest) => rest.strip_prefix(' ').unwrap_or(rest),
        None => t,
    }
}

/// Whether `rest` (the text after `@`) begins a tag name.
fn starts_tag(rest: &str) -> bool {
    rest.starts_with(|c: char| c.is_ascii_alphabetic())
}

/// Split `param int $x the count` into (`"param"`, `"int $x the count"`).
fn split_tag(rest: &str) -> (String, String) {
    let end = rest
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '-' || c == '_'))
        .unwrap_or(rest.len());
    (rest[..end].to_string(), rest[end..].trim().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tag(name: &str, value: &str) -> DocTag {
        DocTag {
            name: name.to_string(),
            value: value.to_string(),
        }
    }

    #[test]
    fn single_line_block() {
        let b = parse_block("/** @return int */");
        assert_eq!(b.description, "");
        assert_eq!(b.tags, [tag("return", "int")]);
    }

    #[test]
    fn description_and_tags() {
        let b = parse_block(
            "/**\n * Builds a thing.\n *\n * @param int $count how many\n * @return Thing\n */",
        );
        assert_eq!(b.description, "Builds a thing.");
        assert_eq!(
            b.tags,
            [tag("param", "int $count how many"), tag("return", "Thing")]
        );
    }

    #[test]
    fn multiline_tag_body_is_space_joined() {
        let b = parse_block(
            "/**\n * @param string $name a very\n *   long description that\n *   wraps\n */",
        );
        assert_eq!(
            b.tags,
            [tag(
                "param",
                "string $name a very long description that wraps"
            )]
        );
    }

    #[test]
    fn multiline_array_shape_reassembles() {
        let b = parse_block("/**\n * @return array{\n *   id: int,\n *   name: string\n * }\n */");
        assert_eq!(b.tags, [tag("return", "array{ id: int, name: string }")]);
    }

    #[test]
    fn prefixed_tag_names_are_preserved() {
        let b = parse_block("/** @phpstan-return list<int> @psalm-param T $x */");
        // Both are on one line, so the first tag absorbs the rest as body; the
        // realistic multi-line form is covered below.
        let b2 = parse_block("/**\n * @phpstan-return list<int>\n * @psalm-param T $x\n */");
        assert_eq!(
            b2.tags,
            [
                tag("phpstan-return", "list<int>"),
                tag("psalm-param", "T $x")
            ]
        );
        assert_eq!(b.tags[0].name, "phpstan-return");
    }

    #[test]
    fn inline_tags_stay_in_description() {
        let b = parse_block("/**\n * See {@see Foo::bar()} for details.\n * @return void\n */");
        assert_eq!(b.description, "See {@see Foo::bar()} for details.");
        assert_eq!(b.tags, [tag("return", "void")]);
    }

    #[test]
    fn html_and_braces_in_prose_do_not_break_anything() {
        let b = parse_block("/**\n * A <p>paragraph</p> with {braces}.\n * @param int $x\n */");
        assert_eq!(b.description, "A <p>paragraph</p> with {braces}.");
        assert_eq!(b.tags, [tag("param", "int $x")]);
    }

    #[test]
    fn empty_block() {
        assert_eq!(parse_block("/** */"), DocBlock::default());
        assert_eq!(parse_block("/**\n *\n */"), DocBlock::default());
    }
}
