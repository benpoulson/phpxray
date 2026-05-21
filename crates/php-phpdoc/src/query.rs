//! Query helpers over raw PHPDoc blocks.
//!
//! Rules often need conservative answers such as "does this block mention a
//! return tag anywhere?" or normalized answers such as "does this tag's base
//! name match after stripping `phpstan-` / `psalm-`?". Centralising those rules
//! keeps PHPDoc semantics from drifting across diagnostics.

use crate::parse_block;

/// Vendor prefix on a PHPDoc tag name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TagPrefix {
    PhpStan,
    Psalm,
}

/// Split a doc tag name into its base and optional supported vendor prefix.
pub fn split_prefix(name: &str) -> (&str, Option<TagPrefix>) {
    if let Some(rest) = name.strip_prefix("phpstan-") {
        (rest, Some(TagPrefix::PhpStan))
    } else if let Some(rest) = name.strip_prefix("psalm-") {
        (rest, Some(TagPrefix::Psalm))
    } else {
        (name, None)
    }
}

/// The base tag name after stripping supported vendor prefixes.
pub fn base_name(name: &str) -> &str {
    split_prefix(name).0
}

/// Precedence for tags that may appear in plain, psalm, and phpstan forms.
pub fn base_priority(name: &str) -> (&str, i8) {
    match split_prefix(name) {
        (base, Some(TagPrefix::PhpStan)) => (base, 2),
        (base, Some(TagPrefix::Psalm)) => (base, 1),
        (base, None) => (base, 0),
    }
}

pub fn tag_matches(name: &str, bases: &[&str]) -> bool {
    bases.contains(&base_name(name))
}

/// Nested `@tag` names found inside a tag value.
pub fn value_tag_names(value: &str) -> impl Iterator<Item = &str> {
    value.match_indices('@').filter_map(|(idx, _)| {
        let rest = &value[idx + 1..];
        let end = rest
            .char_indices()
            .find(|(_, ch)| !(ch.is_ascii_alphanumeric() || *ch == '-' || *ch == '_'))
            .map(|(i, _)| i)
            .unwrap_or(rest.len());
        (end > 0).then_some(&rest[..end])
    })
}

/// Parsed tag lookup with prefix normalization and nested `@tag` value scans.
pub fn has_base_tag(doc: Option<&str>, bases: &[&str]) -> bool {
    let Some(doc) = doc else { return false };
    parse_block(doc).tags.iter().any(|tag| {
        tag_matches(&tag.name, bases)
            || value_tag_names(&tag.value).any(|inner| tag_matches(inner, bases))
    })
}

/// Conservative raw lookup for tags where over-matching only suppresses a
/// diagnostic. `needle` should include the leading `@`.
pub fn raw_contains(doc: Option<&str>, needle: &str) -> bool {
    doc.is_some_and(|d| d.contains(needle))
}

/// Conservative return-tag lookup used by missing native type rules.
pub fn has_return_conservative(doc: Option<&str>) -> bool {
    doc.is_some_and(|d| d.contains("@return") || d.contains("-return"))
}

/// Conservative `@var` lookup used by missing property type rules.
pub fn has_var_conservative(doc: Option<&str>) -> bool {
    raw_contains(doc, "@var")
}

pub fn has_no_named_arguments(doc: Option<&str>) -> bool {
    raw_contains(doc, "@no-named-arguments")
}

/// Conservative scan for an `@param ... $name` tag. Any `@param*` tag mentioning
/// the variable as a whole token before the next tag counts.
pub fn has_param_conservative(doc: Option<&str>, name: &str) -> bool {
    let Some(doc) = doc else { return false };
    let mut search = doc;
    while let Some(off) = search.find("@param") {
        let after = &search[off + "@param".len()..];
        let segment = after.split('@').next().unwrap_or(after);
        if contains_variable_token(segment, name) {
            return true;
        }
        search = after;
    }
    false
}

pub fn contains_variable_token(text: &str, name: &str) -> bool {
    let needle = format!("${name}");
    let bytes = text.as_bytes();
    let nlen = needle.len();
    let mut i = 0;
    while let Some(off) = text[i..].find(&needle) {
        let start = i + off;
        let end = start + nlen;
        let after_ok =
            end >= bytes.len() || !(bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_');
        if after_ok {
            return true;
        }
        i = end;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_supported_prefixes_and_preserves_priority() {
        assert_eq!(split_prefix("param"), ("param", None));
        assert_eq!(
            split_prefix("phpstan-param"),
            ("param", Some(TagPrefix::PhpStan))
        );
        assert_eq!(
            split_prefix("psalm-return"),
            ("return", Some(TagPrefix::Psalm))
        );
        assert_eq!(base_priority("phpstan-param"), ("param", 2));
    }

    #[test]
    fn finds_base_tags_and_nested_value_tags() {
        let doc = "/**\n * @phpstan-pure @psalm-assert string $x\n */";
        assert!(has_base_tag(Some(doc), &["pure"]));
        assert!(has_base_tag(Some(doc), &["assert"]));
        assert!(!has_base_tag(Some(doc), &["impure"]));
    }

    #[test]
    fn param_scan_matches_whole_variable_token() {
        let doc = "/** @param int $id @param string $identifier */";
        assert!(has_param_conservative(Some(doc), "id"));
        assert!(has_param_conservative(Some(doc), "identifier"));
        assert!(!has_param_conservative(
            Some("/** @param int $identifier */"),
            "id"
        ));
    }
}
