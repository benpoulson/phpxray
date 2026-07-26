//! Name resolution for PHP: turn names *as written* into canonical
//! fully-qualified names, following PHP's name-resolution rules.
//!
//! The parser produces a faithful AST in which names are recorded verbatim
//! (with the lexer's `NameFq` classification). This crate is the first semantic
//! pass: given the active namespace and `use` imports, it maps each name to the
//! entity it refers to. It is **non-destructive** — the AST is left untouched
//! and resolution is produced as a separate artifact.
//!
//! PHP has three independent symbol namespaces — **classes**, **functions**, and
//! **constants** — each with its own `use` table and its own rules. Class and
//! function names match case-insensitively; constants are case-sensitive. This
//! module's [`Scope`] holds the per-namespace-block context and resolves names
//! within it; building a `Scope` by walking a program is a later milestone.

use php_ast::{Name, NameFq};

pub mod depsrec;
mod diagnostics;
mod index;
mod references;
pub mod symbols;
pub use diagnostics::diagnostics;
pub use index::{for_each_region, index_file, ClassSymbol, ConstSymbol, FileIndex, FunctionSymbol};
pub use references::{resolve_references, RefKind, ResolvedRef};
pub use symbols::{
    display_fqn, strip_leading_slash, write_ci_key, SymbolKey, SymbolKind, SymbolOrigin,
};

/// What a name resolves to in a given [`Scope`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    /// A definite fully-qualified name (no leading `\`), e.g. `App\Models\User`.
    Fqn(String),
    /// An unqualified function or constant used inside a namespace. PHP resolves
    /// these at runtime: it tries the namespaced name first and falls back to the
    /// global symbol if that is not defined.
    Fallback { namespaced: String, global: String },
    /// `self` / `parent` / `static` — a late-bound class reference resolved
    /// against the enclosing class context, not a namespace.
    LateStatic(String),
    /// A reserved built-in type (`int`, `string`, `void`, …): not a user symbol.
    BuiltinType(String),
}

impl Resolution {
    /// The primary fully-qualified name, if this resolves to one. For a
    /// [`Resolution::Fallback`] this is the namespaced candidate.
    pub fn fqn(&self) -> Option<&str> {
        match self {
            Resolution::Fqn(s) | Resolution::Fallback { namespaced: s, .. } => Some(s),
            Resolution::LateStatic(_) | Resolution::BuiltinType(_) => None,
        }
    }
}

/// The name-resolution context for one namespace block: the current namespace
/// and the three `use` import tables.
#[derive(Debug, Default, Clone)]
pub struct Scope {
    /// The current namespace prefix (no leading/trailing `\`); `None` = global.
    namespace: Option<String>,
    /// Class imports, keyed by lowercased alias → target FQN.
    use_class: Vec<(String, String)>,
    /// Function imports, keyed by lowercased alias → target FQN.
    use_function: Vec<(String, String)>,
    /// Constant imports, keyed by case-sensitive alias → target FQN.
    use_const: Vec<(String, String)>,
}

impl Scope {
    /// A scope in the global namespace with no imports.
    pub fn global() -> Self {
        Self::default()
    }

    /// A scope in namespace `ns` (e.g. `"App\\Models"`) with no imports.
    pub fn in_namespace(ns: impl Into<String>) -> Self {
        Self {
            namespace: Some(ns.into()),
            ..Self::default()
        }
    }

    /// The current namespace prefix, or `None` in the global namespace.
    pub fn namespace(&self) -> Option<&str> {
        self.namespace.as_deref()
    }

    /// Register `use Target as alias;` (class import). `alias`/`target` carry no
    /// leading `\`.
    pub fn add_class_use(&mut self, alias: &str, target: &str) {
        self.use_class
            .push((alias.to_ascii_lowercase(), strip(target).to_string()));
    }

    /// Register `use function Target as alias;`.
    pub fn add_function_use(&mut self, alias: &str, target: &str) {
        self.use_function
            .push((alias.to_ascii_lowercase(), strip(target).to_string()));
    }

    /// Register `use const Target as alias;` (case-sensitive alias).
    pub fn add_const_use(&mut self, alias: &str, target: &str) {
        self.use_const
            .push((alias.to_string(), strip(target).to_string()));
    }

    /// Resolve a name used as a **class-like** reference (`extends`, `new`, `::`,
    /// `instanceof`, type hints, …).
    pub fn resolve_class(&self, name: &Name) -> Resolution {
        let text = strip(&name.text);
        match name.fq {
            NameFq::Fq => Resolution::Fqn(text.to_string()),
            NameFq::Relative => Resolution::Fqn(self.prefix(relative_tail(text))),
            NameFq::NotFq => match split_first(text) {
                // Unqualified single segment.
                (first, None) => {
                    if let Some(special) = late_static(first) {
                        return Resolution::LateStatic(special.to_string());
                    }
                    if is_builtin_type(first) {
                        return Resolution::BuiltinType(first.to_ascii_lowercase());
                    }
                    if let Some(fqn) = lookup_ci(&self.use_class, first) {
                        return Resolution::Fqn(fqn);
                    }
                    Resolution::Fqn(self.prefix(text))
                }
                // Qualified `A\B…`: the first segment may be a class alias.
                (first, Some(rest)) => match lookup_ci(&self.use_class, first) {
                    Some(fqn) => Resolution::Fqn(format!("{fqn}\\{rest}")),
                    None => Resolution::Fqn(self.prefix(text)),
                },
            },
        }
    }

    /// Resolve a name used as a **function** reference (`foo(...)`).
    pub fn resolve_function(&self, name: &Name) -> Resolution {
        self.resolve_callable(name, &self.use_function, true)
    }

    /// Resolve a name used as a **constant** reference (a bare `FOO`). Constant
    /// imports are case-sensitive.
    pub fn resolve_const(&self, name: &Name) -> Resolution {
        self.resolve_callable(name, &self.use_const, false)
    }

    /// Shared logic for functions and constants: like classes, but unqualified
    /// names get PHP's global fallback, and lookups are case-sensitive for
    /// constants.
    fn resolve_callable(&self, name: &Name, imports: &[(String, String)], ci: bool) -> Resolution {
        let text = strip(&name.text);
        match name.fq {
            NameFq::Fq => Resolution::Fqn(text.to_string()),
            NameFq::Relative => Resolution::Fqn(self.prefix(relative_tail(text))),
            NameFq::NotFq => {
                let lookup = |name: &str| {
                    if ci {
                        lookup_ci(imports, name)
                    } else {
                        lookup_cs(imports, name)
                    }
                };
                match split_first(text) {
                    // Unqualified: imported name wins; otherwise namespaced with a
                    // global fallback (just the global name when already global).
                    (first, None) => {
                        if let Some(fqn) = lookup(first) {
                            return Resolution::Fqn(fqn);
                        }
                        match &self.namespace {
                            Some(_) => Resolution::Fallback {
                                namespaced: self.prefix(text),
                                global: text.to_string(),
                            },
                            None => Resolution::Fqn(text.to_string()),
                        }
                    }
                    // Qualified: the first segment names a *namespace*, so it
                    // resolves through the class/namespace import table — never
                    // through `use function`/`use const`, which apply to
                    // unqualified names only. So `use Other\Util; Util\helper()`
                    // is `Other\Util\helper`, while `use function Other\helper;
                    // helper\x()` is the current namespace's `helper\x`.
                    (first, Some(rest)) => match lookup_ci(&self.use_class, first) {
                        Some(fqn) => Resolution::Fqn(format!("{fqn}\\{rest}")),
                        None => Resolution::Fqn(self.prefix(text)),
                    },
                }
            }
        }
    }

    /// The fully-qualified name of a symbol *declared* in this scope (a class,
    /// function, or constant named `local`): the current namespace plus `local`.
    pub fn qualify(&self, local: &str) -> String {
        self.prefix(local)
    }

    /// Prefix `rel` with the current namespace (or return it unchanged in the
    /// global namespace).
    fn prefix(&self, rel: &str) -> String {
        match &self.namespace {
            Some(ns) => format!("{ns}\\{rel}"),
            None => rel.to_string(),
        }
    }
}

/// Strip a single leading namespace separator.
fn strip(s: &str) -> &str {
    s.strip_prefix('\\').unwrap_or(s)
}

/// Split `A\B\C` into (`"A"`, `Some("B\C")`); a single segment yields `None`.
fn split_first(s: &str) -> (&str, Option<&str>) {
    match s.split_once('\\') {
        Some((first, rest)) => (first, Some(rest)),
        None => (s, None),
    }
}

/// For a relative name `namespace\Foo\Bar`, the part after the `namespace\`
/// prefix (`Foo\Bar`).
fn relative_tail(s: &str) -> &str {
    s.split_once('\\').map(|(_, rest)| rest).unwrap_or(s)
}

/// Case-insensitive import lookup (classes, functions).
fn lookup_ci(imports: &[(String, String)], name: &str) -> Option<String> {
    let key = name.to_ascii_lowercase();
    imports
        .iter()
        .rev()
        .find(|(a, _)| *a == key)
        .map(|(_, f)| f.clone())
}

/// Case-sensitive import lookup (constants).
fn lookup_cs(imports: &[(String, String)], name: &str) -> Option<String> {
    imports
        .iter()
        .rev()
        .find(|(a, _)| a == name)
        .map(|(_, f)| f.clone())
}

/// `self` / `parent` / `static` — returned lowercased.
fn late_static(name: &str) -> Option<&'static str> {
    match () {
        _ if name.eq_ignore_ascii_case("self") => Some("self"),
        _ if name.eq_ignore_ascii_case("parent") => Some("parent"),
        _ if name.eq_ignore_ascii_case("static") => Some("static"),
        _ => None,
    }
}

/// Reserved type names that are never class references (so never namespaced).
fn is_builtin_type(name: &str) -> bool {
    const TYPES: &[&str] = &[
        "int", "float", "string", "bool", "void", "iterable", "object", "mixed", "never", "null",
        "false", "true", "array", "callable",
    ];
    TYPES.iter().any(|t| name.eq_ignore_ascii_case(t))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(fq: NameFq, text: &str) -> Name {
        Name {
            span: php_span::Span::at(0),
            fq,
            text: text.to_string(),
        }
    }
    fn unq(text: &str) -> Name {
        n(NameFq::NotFq, text)
    }

    // --- classes ---------------------------------------------------------

    #[test]
    fn unqualified_class_in_namespace_is_prefixed() {
        let s = Scope::in_namespace("App\\Models");
        assert_eq!(
            s.resolve_class(&unq("User")),
            Resolution::Fqn("App\\Models\\User".into())
        );
    }

    #[test]
    fn unqualified_class_in_global_namespace() {
        let s = Scope::global();
        assert_eq!(
            s.resolve_class(&unq("User")),
            Resolution::Fqn("User".into())
        );
    }

    #[test]
    fn fully_qualified_class_strips_leading_backslash() {
        let s = Scope::in_namespace("App");
        assert_eq!(
            s.resolve_class(&n(NameFq::Fq, "\\Other\\Thing")),
            Resolution::Fqn("Other\\Thing".into())
        );
    }

    #[test]
    fn relative_class_uses_current_namespace() {
        let s = Scope::in_namespace("App\\Models");
        assert_eq!(
            s.resolve_class(&n(NameFq::Relative, "namespace\\User")),
            Resolution::Fqn("App\\Models\\User".into())
        );
    }

    #[test]
    fn imported_class_alias_wins() {
        let mut s = Scope::in_namespace("App\\Models");
        s.add_class_use("Id", "Ramsey\\Uuid\\Uuid");
        assert_eq!(
            s.resolve_class(&unq("Id")),
            Resolution::Fqn("Ramsey\\Uuid\\Uuid".into())
        );
    }

    #[test]
    fn class_alias_matching_is_case_insensitive() {
        let mut s = Scope::in_namespace("App");
        s.add_class_use("Str", "App\\Support\\Str");
        assert_eq!(
            s.resolve_class(&unq("STR")),
            Resolution::Fqn("App\\Support\\Str".into())
        );
    }

    #[test]
    fn qualified_class_aliases_first_segment() {
        // `use App\Support; Support\Str` → App\Support\Str
        let mut s = Scope::in_namespace("Other");
        s.add_class_use("Support", "App\\Support");
        assert_eq!(
            s.resolve_class(&unq("Support\\Str")),
            Resolution::Fqn("App\\Support\\Str".into())
        );
    }

    #[test]
    fn qualified_class_without_alias_is_prefixed() {
        let s = Scope::in_namespace("App");
        assert_eq!(
            s.resolve_class(&unq("Sub\\Thing")),
            Resolution::Fqn("App\\Sub\\Thing".into())
        );
    }

    #[test]
    fn self_parent_static_are_late_static() {
        let s = Scope::in_namespace("App");
        assert_eq!(
            s.resolve_class(&unq("self")),
            Resolution::LateStatic("self".into())
        );
        assert_eq!(
            s.resolve_class(&unq("Parent")),
            Resolution::LateStatic("parent".into())
        );
        assert_eq!(
            s.resolve_class(&unq("STATIC")),
            Resolution::LateStatic("static".into())
        );
    }

    #[test]
    fn reserved_types_are_not_namespaced() {
        let s = Scope::in_namespace("App");
        assert_eq!(
            s.resolve_class(&unq("int")),
            Resolution::BuiltinType("int".into())
        );
        assert_eq!(
            s.resolve_class(&unq("STRING")),
            Resolution::BuiltinType("string".into())
        );
    }

    // --- functions -------------------------------------------------------

    #[test]
    fn unqualified_function_in_namespace_has_global_fallback() {
        let s = Scope::in_namespace("App");
        assert_eq!(
            s.resolve_function(&unq("strlen")),
            Resolution::Fallback {
                namespaced: "App\\strlen".into(),
                global: "strlen".into()
            }
        );
    }

    #[test]
    fn unqualified_function_in_global_namespace_is_definite() {
        let s = Scope::global();
        assert_eq!(
            s.resolve_function(&unq("strlen")),
            Resolution::Fqn("strlen".into())
        );
    }

    #[test]
    fn imported_function_has_no_fallback() {
        let mut s = Scope::in_namespace("App");
        s.add_function_use("tap", "App\\helpers\\tap");
        assert_eq!(
            s.resolve_function(&unq("tap")),
            Resolution::Fqn("App\\helpers\\tap".into())
        );
    }

    #[test]
    fn qualified_function_is_prefixed() {
        let s = Scope::in_namespace("App");
        assert_eq!(
            s.resolve_function(&unq("util\\f")),
            Resolution::Fqn("App\\util\\f".into())
        );
    }

    #[test]
    fn qualified_function_resolves_through_a_class_import() {
        // `use Other\Util; Util\helper()` is `Other\Util\helper` — the first
        // segment of a qualified name is a namespace, so it goes through the
        // class import table (oracle-verified against PHP 8.5).
        let mut s = Scope::in_namespace("App");
        s.add_class_use("Util", "Other\\Util");
        assert_eq!(
            s.resolve_function(&unq("Util\\helper")),
            Resolution::Fqn("Other\\Util\\helper".into())
        );
        assert_eq!(
            s.resolve_const(&unq("Util\\FOO")),
            Resolution::Fqn("Other\\Util\\FOO".into())
        );
    }

    #[test]
    fn function_import_does_not_apply_to_qualified_names() {
        // `use function Other\helper; helper\x()` is `App\helper\x`: function and
        // constant imports bind unqualified names only.
        let mut s = Scope::in_namespace("App");
        s.add_function_use("helper", "Other\\helper");
        assert_eq!(
            s.resolve_function(&unq("helper\\x")),
            Resolution::Fqn("App\\helper\\x".into())
        );
        let mut c = Scope::in_namespace("App");
        c.add_const_use("C", "Other\\C");
        assert_eq!(
            c.resolve_const(&unq("C\\FOO")),
            Resolution::Fqn("App\\C\\FOO".into())
        );
    }

    // --- constants -------------------------------------------------------

    #[test]
    fn unqualified_const_in_namespace_has_global_fallback() {
        let s = Scope::in_namespace("App");
        assert_eq!(
            s.resolve_const(&unq("PHP_EOL")),
            Resolution::Fallback {
                namespaced: "App\\PHP_EOL".into(),
                global: "PHP_EOL".into()
            }
        );
    }

    #[test]
    fn const_imports_are_case_sensitive() {
        let mut s = Scope::in_namespace("App");
        s.add_const_use("FOO", "Other\\FOO");
        // Exact match resolves; a different case does not.
        assert_eq!(
            s.resolve_const(&unq("FOO")),
            Resolution::Fqn("Other\\FOO".into())
        );
        assert_eq!(
            s.resolve_const(&unq("foo")),
            Resolution::Fallback {
                namespaced: "App\\foo".into(),
                global: "foo".into()
            }
        );
    }

    #[test]
    fn fully_qualified_function_and_const() {
        let s = Scope::in_namespace("App");
        assert_eq!(
            s.resolve_function(&n(NameFq::Fq, "\\strlen")),
            Resolution::Fqn("strlen".into())
        );
        assert_eq!(
            s.resolve_const(&n(NameFq::Fq, "\\PHP_EOL")),
            Resolution::Fqn("PHP_EOL".into())
        );
    }
}
