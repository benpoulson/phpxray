//! Reading `@tag`s off a raw docblock, in one place.
//!
//! Several rule families ask the same three questions of a docblock — what
//! `@template`s does it declare, does this tag name carry a vendor prefix, and
//! what types does a given tag hold. They each used to answer them privately,
//! which is how the crate ended up with two spellings of prefix-stripping and
//! three of "the templates this block declares".
//!
//! The type-bearing helpers come in a raw and a resolved flavour: some rules
//! want the PHPDoc syntax tree (to inspect what was *written*), others want it
//! resolved against a scope (to reason about what it *means*).

use php_reflect::resolve_doc_type;
use php_resolve::Scope;
use php_types::Type;

/// A tag's base name and the vendor prefix it was written with, as a label
/// suitable for a diagnostic message (`"phpstan"` / `"psalm"`).
pub(crate) fn prefix_label(name: &str) -> (&str, Option<&'static str>) {
    match php_phpdoc::query::split_prefix(name) {
        (base, Some(php_phpdoc::query::TagPrefix::PhpStan)) => (base, Some("phpstan")),
        (base, Some(php_phpdoc::query::TagPrefix::Psalm)) => (base, Some("psalm")),
        (base, None) => (base, None),
    }
}

/// The `@template` names a docblock declares.
pub(crate) fn templates(doc: Option<&str>) -> Vec<String> {
    doc.map(php_phpdoc::parse)
        .unwrap_or_default()
        .templates
        .into_iter()
        .map(|t| t.name)
        .collect()
}

/// A method's templates: the class's, plus any the method declares itself.
pub(crate) fn combined_templates(
    class_templates: &[String],
    method_doc: Option<&str>,
) -> Vec<String> {
    let mut out = class_templates.to_vec();
    out.extend(templates(method_doc));
    out
}

/// The types written on every `@<base>` tag (any vendor prefix), unresolved.
pub(crate) fn tag_types(doc_raw: &str, base: &str) -> Vec<php_phpdoc::DocType> {
    php_phpdoc::parse_block(doc_raw)
        .tags
        .iter()
        .filter_map(|tag| {
            if prefix_label(&tag.name).0 != base {
                return None;
            }
            php_phpdoc::parse_type_prefix(&tag.value).map(|(ty, _)| ty)
        })
        .collect()
}

/// [`tag_types`] resolved against `scope`, for rules reasoning about meaning
/// rather than syntax.
pub(crate) fn resolved_tag_types(
    scope: &Scope,
    templates: &[String],
    doc_raw: &str,
    base: &str,
) -> Vec<Type> {
    tag_types(doc_raw, base)
        .iter()
        .map(|ty| resolve_doc_type(scope, templates, ty))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vendor_prefixes_are_labelled_and_stripped() {
        assert_eq!(prefix_label("phpstan-param"), ("param", Some("phpstan")));
        assert_eq!(prefix_label("psalm-param"), ("param", Some("psalm")));
        assert_eq!(prefix_label("param"), ("param", None));
        // Not a vendor prefix we honour — left intact.
        assert_eq!(prefix_label("phan-param"), ("phan-param", None));
    }

    /// A prefixed tag is collected under its base name, which is what makes
    /// `@phpstan-mixin` and `@mixin` interchangeable to the rules.
    #[test]
    fn tag_types_collect_across_vendor_prefixes() {
        let doc = "/**\n * @mixin Foo\n * @phpstan-mixin Bar\n * @return Baz\n */";
        let found: Vec<String> = tag_types(doc, "mixin")
            .iter()
            .map(|t| format!("{t:?}"))
            .collect();
        assert_eq!(found.len(), 2, "{found:?}");
    }

    #[test]
    fn templates_come_from_the_block_and_compose_with_the_class() {
        let class = templates(Some("/**\n * @template T\n */"));
        assert_eq!(class, vec!["T".to_string()]);
        assert_eq!(
            combined_templates(&class, Some("/**\n * @template U\n */")),
            vec!["T".to_string(), "U".to_string()]
        );
        assert!(templates(None).is_empty());
    }
}
