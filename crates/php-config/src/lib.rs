//! M-C0: the analyzer's **YAML configuration**.
//!
//! Our own config file (not a phpstan/NEON drop-in) using vocabulary familiar to
//! phpstan users: `level`, `paths`, `exclude`, `ignore`, … Deserialized with
//! serde; unknown keys are ignored for forward-compatibility. The engine
//! ([`php-cli`]) consumes the resolved [`Config`] to discover files, pick rules
//! by level, and suppress findings.

use regex::Regex;
use serde::de::{self, Deserializer};
use serde::Deserialize;

/// A resolved analyzer configuration.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct Config {
    /// Strictness level (0–9, or `max` = 10). Higher = more rules.
    pub level: Level,
    /// Files/directories to analyze (relative to the config file / project root).
    pub paths: Vec<String>,
    /// Files/directories to parse for symbols only. These files are indexed and
    /// reflected, but diagnostics from them are not reported.
    pub scan_paths: Vec<String>,
    /// Individual files to parse for symbols only.
    pub scan_files: Vec<String>,
    /// Glob patterns to exclude from analysis (`fnmatch`-style; `*`, `**`, `?`).
    pub exclude: Vec<String>,
    /// File extensions to analyze (without the dot). Defaults to `["php"]`.
    pub extensions: Vec<String>,
    /// Target PHP version (e.g. `"8.4"`), if pinned.
    pub php_version: Option<String>,
    /// Path to a baseline file of findings to ignore.
    pub baseline: Option<String>,
    /// Report `ignore` entries that matched nothing (default: true).
    pub report_unmatched_ignored: bool,
    /// Treat PHPDoc types as certain for the always-true/impossible-type rules
    /// (phpstan's `treatPhpDocTypesAsCertain`; default `true`). When `false`, those
    /// rules don't fire on redundancies that are only provable via PHPDoc-derived
    /// types — matching projects that opt out (e.g. nikic/PHP-Parser).
    #[serde(rename = "treatPhpDocTypesAsCertain")]
    pub treat_phpdoc_types_as_certain: bool,
    /// Suppression entries.
    pub ignore: Vec<IgnoreEntry>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            level: Level(0),
            paths: Vec::new(),
            scan_paths: Vec::new(),
            scan_files: Vec::new(),
            exclude: Vec::new(),
            extensions: vec!["php".to_string()],
            php_version: None,
            baseline: None,
            report_unmatched_ignored: true,
            treat_phpdoc_types_as_certain: true,
            ignore: Vec::new(),
        }
    }
}

impl Config {
    /// Parse a config from a YAML string.
    pub fn from_yaml(yaml: &str) -> Result<Config, ConfigError> {
        serde_yaml::from_str(yaml).map_err(ConfigError::Parse)
    }

    /// Load a config from a file path.
    pub fn load(path: impl AsRef<std::path::Path>) -> Result<Config, ConfigError> {
        let text = std::fs::read_to_string(path).map_err(ConfigError::Io)?;
        Config::from_yaml(&text)
    }

    /// Find a config file in `dir`, trying the standard names in order.
    pub fn discover(dir: impl AsRef<std::path::Path>) -> Option<std::path::PathBuf> {
        let dir = dir.as_ref();
        for name in [
            "phpanalyzer.yaml",
            "phpanalyzer.yml",
            "phpanalyzer.dist.yaml",
        ] {
            let p = dir.join(name);
            if p.is_file() {
                return Some(p);
            }
        }
        None
    }
}

/// A strictness level: 0–9, or `max` (10).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Level(pub u8);

impl Level {
    /// The highest level (`max`).
    pub const MAX: Level = Level(10);

    /// The numeric value (0–10).
    pub fn value(self) -> u8 {
        self.0
    }
}

impl<'de> Deserialize<'de> for Level {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            Int(i64),
            Str(String),
        }
        match Repr::deserialize(d)? {
            Repr::Int(n) if (0..=10).contains(&n) => Ok(Level(n as u8)),
            Repr::Int(n) => Err(de::Error::custom(format!(
                "level {n} is out of range (0–9 or \"max\")"
            ))),
            Repr::Str(s) if s.eq_ignore_ascii_case("max") => Ok(Level::MAX),
            Repr::Str(s) => Err(de::Error::custom(format!(
                "invalid level {s:?} (expected 0–9 or \"max\")"
            ))),
        }
    }
}

/// A suppression entry: drop findings matching all of the present fields.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct IgnoreEntry {
    /// A regex matched against the message (with optional `/…/` delimiters).
    pub message: Option<String>,
    /// An exact error identifier (e.g. `return.type`).
    pub identifier: Option<String>,
    /// A single path glob the finding's file must match.
    pub path: Option<String>,
    /// Multiple path globs (any match).
    pub paths: Vec<String>,
    /// Expected number of occurrences (for baselines / strict ignores).
    pub count: Option<usize>,
}

impl<'de> Deserialize<'de> for IgnoreEntry {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        // An entry is either a bare message-regex string or a map.
        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase")]
        struct Map {
            message: Option<String>,
            identifier: Option<String>,
            path: Option<String>,
            #[serde(default)]
            paths: Vec<String>,
            count: Option<usize>,
        }
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            Str(String),
            Map(Map),
        }
        Ok(match Repr::deserialize(d)? {
            Repr::Str(s) => IgnoreEntry {
                message: Some(s),
                ..Default::default()
            },
            Repr::Map(m) => IgnoreEntry {
                message: m.message,
                identifier: m.identifier,
                path: m.path,
                paths: m.paths,
                count: m.count,
            },
        })
    }
}

/// A compiled set of exclude globs, for fast repeated path checks.
pub struct ExcludeMatcher {
    regexes: Vec<Regex>,
}

impl ExcludeMatcher {
    /// Compile `patterns` (glob syntax) into a matcher. Each pattern also matches
    /// paths *under* it (so a bare directory `tests/fixtures` excludes its files).
    pub fn new(patterns: &[String]) -> ExcludeMatcher {
        let mut regexes = Vec::new();
        for p in patterns {
            if let Ok(re) = Regex::new(&glob_to_regex(p)) {
                regexes.push(re);
            }
            // A plain (glob-free) path is treated as a directory: also exclude
            // everything under it. A pattern that already contains globs is used
            // verbatim (fnmatch semantics), so we don't widen it.
            if !p.contains(['*', '?']) {
                let dir = p.trim_end_matches('/');
                if let Ok(re) = Regex::new(&glob_to_regex(&format!("{dir}/**"))) {
                    regexes.push(re);
                }
            }
        }
        ExcludeMatcher { regexes }
    }

    /// Whether `path` matches any exclude pattern (forward slashes normalized).
    pub fn is_excluded(&self, path: &str) -> bool {
        let p = path.replace('\\', "/");
        self.regexes.iter().any(|r| r.is_match(&p))
    }
}

/// Translate an `fnmatch`-style glob to an anchored regex.
/// `**` matches across `/`, `**/` matches zero or more directories, `*` matches
/// within a path segment, `?` matches one non-`/` character.
pub fn glob_to_regex(glob: &str) -> String {
    let mut re = String::from("(?s)^");
    let mut chars = glob.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '*' => {
                if chars.peek() == Some(&'*') {
                    chars.next(); // second '*'
                    if chars.peek() == Some(&'/') {
                        chars.next(); // '**/' = zero or more directories
                        re.push_str("(?:.*/)?");
                    } else {
                        re.push_str(".*");
                    }
                } else {
                    re.push_str("[^/]*");
                }
            }
            '?' => re.push_str("[^/]"),
            '.' | '+' | '(' | ')' | '|' | '[' | ']' | '{' | '}' | '^' | '$' | '\\' => {
                re.push('\\');
                re.push(c);
            }
            other => re.push(other),
        }
    }
    re.push('$');
    re
}

/// An error loading or parsing a config.
#[derive(Debug)]
pub enum ConfigError {
    Io(std::io::Error),
    Parse(serde_yaml::Error),
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConfigError::Io(e) => write!(f, "reading config: {e}"),
            ConfigError::Parse(e) => write!(f, "parsing config: {e}"),
        }
    }
}

impl std::error::Error for ConfigError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_representative_config() {
        let cfg = Config::from_yaml(
            r#"
level: 6
paths:
  - src
  - tests
scanPaths:
  - vendor
scanFiles:
  - generated/stubs.php
exclude:
  - tests/fixtures
  - "**/generated/*"
phpVersion: "8.4"
ignore:
  - "/Cannot call method .* on null/"
  - { identifier: return.type, path: src/Generated }
"#,
        )
        .unwrap();
        assert_eq!(cfg.level, Level(6));
        assert_eq!(cfg.paths, ["src", "tests"]);
        assert_eq!(cfg.scan_paths, ["vendor"]);
        assert_eq!(cfg.scan_files, ["generated/stubs.php"]);
        assert_eq!(cfg.exclude, ["tests/fixtures", "**/generated/*"]);
        assert_eq!(cfg.extensions, ["php"]); // default
        assert_eq!(cfg.php_version.as_deref(), Some("8.4"));
        assert!(cfg.report_unmatched_ignored); // default true
        assert_eq!(cfg.ignore.len(), 2);
        assert_eq!(
            cfg.ignore[0].message.as_deref(),
            Some("/Cannot call method .* on null/")
        );
        assert_eq!(cfg.ignore[1].identifier.as_deref(), Some("return.type"));
        assert_eq!(cfg.ignore[1].path.as_deref(), Some("src/Generated"));
    }

    #[test]
    fn level_accepts_int_and_max() {
        assert_eq!(Config::from_yaml("level: 0").unwrap().level, Level(0));
        assert_eq!(Config::from_yaml("level: max").unwrap().level, Level::MAX);
        assert_eq!(Config::from_yaml("level: MAX").unwrap().level, Level(10));
        assert!(Config::from_yaml("level: 99").is_err());
        assert!(Config::from_yaml("level: nonsense").is_err());
    }

    #[test]
    fn empty_config_uses_defaults() {
        let cfg = Config::from_yaml("{}").unwrap();
        assert_eq!(cfg.level, Level(0));
        assert_eq!(cfg.extensions, ["php"]);
        assert!(cfg.report_unmatched_ignored);
        assert!(cfg.paths.is_empty());
        assert!(cfg.scan_paths.is_empty());
        assert!(cfg.scan_files.is_empty());
    }

    #[test]
    fn unknown_keys_are_ignored() {
        // Forward-compat: keys we don't know about don't break loading.
        let cfg = Config::from_yaml("level: 2\nsomeFutureKey: { a: 1 }\n").unwrap();
        assert_eq!(cfg.level, Level(2));
    }

    #[test]
    fn glob_translation() {
        assert_eq!(glob_to_regex("*.php"), "(?s)^[^/]*\\.php$");
        assert_eq!(glob_to_regex("a/b"), "(?s)^a/b$");
        assert_eq!(glob_to_regex("**/x"), "(?s)^(?:.*/)?x$");
    }

    #[test]
    fn exclude_matching() {
        let m = ExcludeMatcher::new(&["tests/fixtures".into(), "**/generated/*".into()]);
        // Bare directory excludes its files but not siblings.
        assert!(m.is_excluded("tests/fixtures/foo.php"));
        assert!(m.is_excluded("tests/fixtures"));
        assert!(!m.is_excluded("tests/foo.php"));
        // `**/generated/*` matches with or without leading dirs, but not deeper.
        assert!(m.is_excluded("a/b/generated/x.php"));
        assert!(m.is_excluded("generated/x.php"));
        assert!(!m.is_excluded("a/generated/sub/x.php"));
        assert!(!m.is_excluded("src/User.php"));
    }
}
