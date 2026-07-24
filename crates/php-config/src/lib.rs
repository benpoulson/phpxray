//! M-C0: the analyzer's **YAML configuration**.
//!
//! Our own config file (not a phpstan/NEON drop-in) using vocabulary familiar to
//! phpstan users: `level`, `paths`, `exclude`, `ignore`, … Deserialized with
//! serde; unknown keys are ignored for forward-compatibility. The engine
//! ([`phpxray`]) consumes the resolved [`Config`] to discover files, pick rules
//! by level, and suppress findings.
//!
//! The [`neon`] module additionally reads phpstan's `phpstan-baseline.neon`
//! format, so a migrating project's existing baseline loads unchanged.

use regex::Regex;
use serde::de::{self, Deserializer};
use serde::Deserialize;
use std::fmt;
use std::str::FromStr;

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
    /// PHPStan-style exclusion split. `analyse` demotes matching files to
    /// scan-only; `analyseAndScan` drops matching files entirely.
    pub exclude_paths: ExcludePaths,
    /// File extensions to analyze (without the dot). Defaults to `["php"]`.
    pub extensions: Vec<String>,
    /// Target PHP version, if pinned. Accepts `"8.4"`, a phpstan version id
    /// (`80400`), or a `{min, max}` range (normalized to the range minimum).
    #[serde(deserialize_with = "de_php_version")]
    pub php_version: Option<String>,
    /// Path to a baseline file of findings to ignore.
    pub baseline: Option<String>,
    /// Result-cache directory, relative to the project root (default:
    /// `.phpxray/cache/results-v1`). phpstan's `resultCachePath`.
    pub result_cache_path: Option<String>,
    /// Functions that never return (`dd`, `abort`) — branches calling them
    /// terminate like `throw`. phpstan's `earlyTerminatingFunctionCalls`.
    pub early_terminating_function_calls: Vec<String>,
    /// Methods that never return, keyed by class (phpstan's
    /// `earlyTerminatingMethodCalls`: `{ "PHPUnit\\Framework\\TestCase": ["fail"] }`).
    pub early_terminating_method_calls: std::collections::HashMap<String, Vec<String>>,
    /// Editor link template shown under each table finding (`%file%`,
    /// `%relFile%`, `%line%`, `%column%` placeholders). phpstan's `editorUrl`.
    pub editor_url: Option<String>,
    /// Display text for the editor link (phpstan's `editorUrlTitle`).
    pub editor_url_title: Option<String>,
    /// Report `ignore` entries that matched nothing (default: true).
    pub report_unmatched_ignored: bool,
    /// Treat PHPDoc types as certain for the always-true/impossible-type rules
    /// (phpstan's `treatPhpDocTypesAsCertain`; default `true`). When `false`, those
    /// rules don't fire on redundancies that are only provable via PHPDoc-derived
    /// types — matching projects that opt out (e.g. nikic/PHP-Parser).
    #[serde(rename = "treatPhpDocTypesAsCertain")]
    pub treat_phpdoc_types_as_certain: bool,
    /// Infer signatures for fully untyped functions/methods from their bodies and
    /// call sites (default `true`). Treated as PHPDoc-grade: refines inference for
    /// legacy untyped code without affecting native-level (`treatPhpDocTypesAsCertain:
    /// false`) checking. Set `false` to analyze declarations only, like PHPStan.
    pub infer_untyped_signatures: bool,
    /// User-supplied stub files (`.stub`/`.php`), parsed with our own front end
    /// and indexed *after* project source so their declarations win over (or fill
    /// in) reflection for the named symbols — the standard way to correct or
    /// supply third-party signatures. Paths resolve relative to the project root.
    /// Mirrors PHPStan's `parameters.stubFiles`.
    pub stub_files: Vec<String>,
    /// Global type aliases (`typeAliases: { AliasName: 'int|string' }`). Each
    /// alias name is usable unqualified in any PHPDoc; expanded into reflected
    /// member/function types after indexing (a real class of the same name wins,
    /// keeping the collision FP-safe). Mirrors PHPStan's `parameters.typeAliases`.
    pub type_aliases: std::collections::HashMap<String, String>,
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
            exclude_paths: ExcludePaths::default(),
            extensions: vec!["php".to_string()],
            php_version: None,
            baseline: None,
            result_cache_path: None,
            early_terminating_function_calls: Vec::new(),
            early_terminating_method_calls: std::collections::HashMap::new(),
            editor_url: None,
            editor_url_title: None,
            report_unmatched_ignored: true,
            treat_phpdoc_types_as_certain: true,
            infer_untyped_signatures: true,
            stub_files: Vec::new(),
            type_aliases: std::collections::HashMap::new(),
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
            "phpxray.yaml",
            "phpxray.yml",
            "phpxray.dist.yaml",
        ] {
            let p = dir.join(name);
            if p.is_file() {
                return Some(p);
            }
        }
        None
    }
}

/// PHPStan-style path exclusions.
#[derive(Debug, Clone, Default, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", default)]
pub struct ExcludePaths {
    /// Exclude from rule analysis, but still scan/index/reflect.
    pub analyse: Vec<String>,
    /// Exclude from both rule analysis and scan/index/reflect.
    pub analyse_and_scan: Vec<String>,
}

/// A strictness level: 0–9, or `max` (internally 10).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Level(pub u8);

impl Level {
    /// The highest level (`max`).
    pub const MAX: Level = Level(10);

    /// The numeric value (0–10).
    pub fn value(self) -> u8 {
        self.0
    }

    /// Level-derived rule switches. This is the single place where product
    /// strictness turns into rule-engine options.
    pub fn rule_options(self) -> RuleOptions {
        RuleOptions {
            // phpstan's `checkUnionTypes` / `reportMaybes` turns on at level 7.
            report_maybes: self.0 >= 7,
            // phpstan's `checkNullables` turns on at level 8.
            check_nullables: self.0 >= 8,
            // Strict mixed checks turn on after nullable checks.
            check_explicit_mixed: self.0 >= 9,
            check_implicit_mixed: self.0 >= Self::MAX.0,
        }
    }
}

/// Rule-engine switches derived from [`Level`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RuleOptions {
    pub report_maybes: bool,
    pub check_nullables: bool,
    pub check_explicit_mixed: bool,
    pub check_implicit_mixed: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseLevelError {
    value: String,
}

impl fmt::Display for ParseLevelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid level {:?} (expected 0–9 or \"max\")",
            self.value
        )
    }
}

impl std::error::Error for ParseLevelError {}

impl FromStr for Level {
    type Err = ParseLevelError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.eq_ignore_ascii_case("max") {
            return Ok(Level::MAX);
        }
        match s.parse::<u8>() {
            Ok(n) if n <= 9 => Ok(Level(n)),
            _ => Err(ParseLevelError {
                value: s.to_string(),
            }),
        }
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == Level::MAX {
            f.write_str("max")
        } else {
            write!(f, "{}", self.0)
        }
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
            Repr::Int(n) if (0..=9).contains(&n) => Ok(Level(n as u8)),
            Repr::Int(n) => Err(de::Error::custom(format!(
                "level {n} is out of range (0–9 or \"max\")"
            ))),
            Repr::Str(s) => s.parse::<Level>().map_err(de::Error::custom),
        }
    }
}

/// A suppression entry: drop findings matching all of the present fields.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct IgnoreEntry {
    /// A regex matched against the message (with optional `/…/` delimiters).
    pub message: Option<String>,
    /// Multiple message regexes (any match).
    pub messages: Vec<String>,
    /// A literal message matched by string equality, not as a regex
    /// (phpstan's `rawMessage`).
    pub raw_message: Option<String>,
    /// Multiple literal messages (any match).
    pub raw_messages: Vec<String>,
    /// An exact error identifier (e.g. `return.type`).
    pub identifier: Option<String>,
    /// Multiple identifiers (any match).
    pub identifiers: Vec<String>,
    /// A single path glob the finding's file must match.
    pub path: Option<String>,
    /// Multiple path globs (any match).
    pub paths: Vec<String>,
    /// Expected number of occurrences (for baselines / strict ignores).
    pub count: Option<usize>,
    /// Per-entry override of `reportUnmatchedIgnored` (phpstan's per-entry
    /// `reportUnmatched`). `None` = follow the global setting. Baseline-loaded
    /// entries default to `Some(false)`: a baseline is a snapshot of past debt,
    /// so an entry going stale means the code got *fixed* — nagging about it
    /// would punish progress.
    pub report_unmatched: Option<bool>,
}

impl<'de> Deserialize<'de> for IgnoreEntry {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        // An entry is either a bare message-regex string or a map.
        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase")]
        struct Map {
            message: Option<String>,
            #[serde(default)]
            messages: Vec<String>,
            raw_message: Option<String>,
            #[serde(default)]
            raw_messages: Vec<String>,
            identifier: Option<String>,
            #[serde(default)]
            identifiers: Vec<String>,
            path: Option<String>,
            #[serde(default)]
            paths: Vec<String>,
            count: Option<usize>,
            report_unmatched: Option<bool>,
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
                messages: m.messages,
                raw_message: m.raw_message,
                raw_messages: m.raw_messages,
                identifier: m.identifier,
                identifiers: m.identifiers,
                path: m.path,
                paths: m.paths,
                count: m.count,
                report_unmatched: m.report_unmatched,
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
                if !dir.contains('/') {
                    if let Ok(re) = Regex::new(&glob_to_regex(&format!("**/{dir}"))) {
                        regexes.push(re);
                    }
                    if let Ok(re) = Regex::new(&glob_to_regex(&format!("**/{dir}/**"))) {
                        regexes.push(re);
                    }
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

/// `phpVersion` accepts a string (`"8.4"`), a phpstan version id (`80400`),
/// or a `{min, max}` range. Ranges normalize to the minimum: analysis against
/// the lowest supported version is the conservative choice until per-version
/// range checking exists.
fn de_php_version<'de, D: Deserializer<'de>>(d: D) -> Result<Option<String>, D::Error> {
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum Bound {
        Int(u64),
        Str(String),
    }
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum Raw {
        Int(u64),
        Str(String),
        Range { min: Option<Bound>, max: Option<Bound> },
    }
    fn norm(b: Bound) -> String {
        match b {
            Bound::Int(id) => format!("{}.{}", id / 10_000, (id / 100) % 100),
            Bound::Str(s) => s,
        }
    }
    Ok(match Option::<Raw>::deserialize(d)? {
        None => None,
        Some(Raw::Int(id)) => Some(norm(Bound::Int(id))),
        Some(Raw::Str(s)) => Some(s),
        Some(Raw::Range { min, max }) => min.or(max).map(norm),
    })
}

pub mod neon;

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
excludePaths:
  analyse:
    - vendor
  analyseAndScan:
    - storage
    - bootstrap/cache
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
        assert_eq!(cfg.exclude_paths.analyse, ["vendor"]);
        assert_eq!(
            cfg.exclude_paths.analyse_and_scan,
            ["storage", "bootstrap/cache"]
        );
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
    fn php_version_accepts_string_int_and_range() {
        assert_eq!(
            Config::from_yaml("phpVersion: \"8.4\"").unwrap().php_version.as_deref(),
            Some("8.4")
        );
        assert_eq!(
            Config::from_yaml("phpVersion: 80400").unwrap().php_version.as_deref(),
            Some("8.4")
        );
        assert_eq!(
            Config::from_yaml("phpVersion: 70125").unwrap().php_version.as_deref(),
            Some("7.1")
        );
        assert_eq!(
            Config::from_yaml("phpVersion:\n  min: 80100\n  max: 80400\n")
                .unwrap()
                .php_version
                .as_deref(),
            Some("8.1")
        );
        assert_eq!(
            Config::from_yaml("phpVersion:\n  max: 80400\n")
                .unwrap()
                .php_version
                .as_deref(),
            Some("8.4")
        );
    }

    #[test]
    fn editor_url_and_cache_path_fields() {
        let cfg = Config::from_yaml(
            "editorUrl: \"phpstorm://open?file=%file%&line=%line%\"\neditorUrlTitle: \"open\"\nresultCachePath: var/cache\n",
        )
        .unwrap();
        assert_eq!(
            cfg.editor_url.as_deref(),
            Some("phpstorm://open?file=%file%&line=%line%")
        );
        assert_eq!(cfg.editor_url_title.as_deref(), Some("open"));
        assert_eq!(cfg.result_cache_path.as_deref(), Some("var/cache"));
    }

    #[test]
    fn level_accepts_int_and_max() {
        assert_eq!(Config::from_yaml("level: 0").unwrap().level, Level(0));
        assert_eq!(Config::from_yaml("level: max").unwrap().level, Level::MAX);
        assert_eq!(Config::from_yaml("level: MAX").unwrap().level, Level(10));
        assert!(Config::from_yaml("level: 10").is_err());
        assert!(Config::from_yaml("level: 99").is_err());
        assert!(Config::from_yaml("level: nonsense").is_err());
    }

    #[test]
    fn level_from_str_display_and_rule_options_are_canonical() {
        assert_eq!("8".parse::<Level>().unwrap(), Level(8));
        assert_eq!("max".parse::<Level>().unwrap(), Level::MAX);
        assert!("10".parse::<Level>().is_err());
        assert_eq!(Level(8).to_string(), "8");
        assert_eq!(Level::MAX.to_string(), "max");
        assert!(!Level(6).rule_options().report_maybes);
        assert!(Level(7).rule_options().report_maybes);
        assert!(!Level(7).rule_options().check_nullables);
        assert!(Level(8).rule_options().check_nullables);
        assert!(!Level(8).rule_options().check_explicit_mixed);
        assert!(Level(9).rule_options().check_explicit_mixed);
        assert!(!Level(9).rule_options().check_implicit_mixed);
        assert!(Level::MAX.rule_options().check_implicit_mixed);
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
        assert!(cfg.exclude_paths.analyse.is_empty());
        assert!(cfg.exclude_paths.analyse_and_scan.is_empty());
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
        let m = ExcludeMatcher::new(&[
            "tests/fixtures".into(),
            "**/generated/*".into(),
            "vendor".into(),
        ]);
        // Bare directory excludes its files but not siblings.
        assert!(m.is_excluded("tests/fixtures/foo.php"));
        assert!(m.is_excluded("tests/fixtures"));
        assert!(!m.is_excluded("tests/foo.php"));
        // A single bare directory name also excludes that directory at any depth.
        assert!(m.is_excluded("vendor/composer/ClassLoader.php"));
        assert!(m.is_excluded("packages/tool/vendor/composer/ClassLoader.php"));
        assert!(!m.is_excluded("packages/tool/not-vendor/ClassLoader.php"));
        // `**/generated/*` matches with or without leading dirs, but not deeper.
        assert!(m.is_excluded("a/b/generated/x.php"));
        assert!(m.is_excluded("generated/x.php"));
        assert!(!m.is_excluded("a/generated/sub/x.php"));
        assert!(!m.is_excluded("src/User.php"));
    }
}
