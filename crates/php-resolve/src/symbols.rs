//! Shared symbol identity helpers.
//!
//! PHP has separate symbol namespaces with different comparison rules. Keeping
//! those rules here prevents every downstream layer from growing its own
//! slightly-different `trim_start_matches('\\').to_ascii_lowercase()` helper.

use std::fmt;

/// The PHP symbol namespace a name belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    /// Classes, interfaces, traits, and enums. PHP matches these
    /// case-insensitively.
    ClassLike,
    /// Functions. PHP matches these case-insensitively.
    Function,
    /// Constants. PHP user constants are case-sensitive.
    Constant,
}

impl SymbolKind {
    /// Whether this symbol kind uses case-sensitive lookup.
    pub fn is_case_sensitive(self) -> bool {
        matches!(self, SymbolKind::Constant)
    }
}

/// Canonical map key for a PHP symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymbolKey {
    kind: SymbolKind,
    text: String,
}

impl SymbolKey {
    pub fn new(kind: SymbolKind, fqn: impl AsRef<str>) -> Self {
        let normalized = strip_leading_slash(fqn.as_ref());
        let text = if kind.is_case_sensitive() {
            normalized.to_string()
        } else {
            normalized.to_ascii_lowercase()
        };
        Self { kind, text }
    }

    pub fn class_like(fqn: impl AsRef<str>) -> Self {
        Self::new(SymbolKind::ClassLike, fqn)
    }

    pub fn function(fqn: impl AsRef<str>) -> Self {
        Self::new(SymbolKind::Function, fqn)
    }

    pub fn constant(fqn: impl AsRef<str>) -> Self {
        Self::new(SymbolKind::Constant, fqn)
    }

    pub fn kind(&self) -> SymbolKind {
        self.kind
    }

    pub fn as_str(&self) -> &str {
        &self.text
    }

    pub fn into_string(self) -> String {
        self.text
    }

    pub fn same(kind: SymbolKind, a: impl AsRef<str>, b: impl AsRef<str>) -> bool {
        Self::new(kind, a).text == Self::new(kind, b).text
    }
}

impl fmt::Display for SymbolKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.text)
    }
}

/// Where a symbol came from in the analyzer pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolOrigin {
    /// User-facing analyzed source. May shadow built-ins.
    Analyzed,
    /// Symbol-provider-only source. Must not shadow curated built-ins.
    Scan,
    /// Curated built-in manifests.
    Builtin,
}

impl SymbolOrigin {
    pub fn label(self) -> &'static str {
        match self {
            SymbolOrigin::Analyzed => "analyzed",
            SymbolOrigin::Scan => "scan",
            SymbolOrigin::Builtin => "builtin",
        }
    }
}

/// Drop leading namespace separators for display/canonical storage.
pub fn strip_leading_slash(fqn: &str) -> &str {
    fqn.trim_start_matches('\\')
}

/// Display-normalize an FQN while preserving case.
pub fn display_fqn(fqn: impl AsRef<str>) -> String {
    strip_leading_slash(fqn.as_ref()).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_and_function_keys_are_case_insensitive() {
        assert_eq!(
            SymbolKey::class_like("\\App\\User"),
            SymbolKey::class_like("app\\user")
        );
        assert_eq!(
            SymbolKey::function("App\\HELPER"),
            SymbolKey::function("app\\helper")
        );
    }

    #[test]
    fn constant_keys_are_case_sensitive() {
        assert_ne!(
            SymbolKey::constant("App\\LIMIT"),
            SymbolKey::constant("App\\limit")
        );
        assert_eq!(SymbolKey::constant("\\App\\LIMIT").as_str(), "App\\LIMIT");
    }
}
