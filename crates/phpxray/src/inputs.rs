//! The single registration point for **analysis inputs**.
//!
//! Anything that can change the *output* of analysis used to be mirrored across
//! four uncoupled sites: the batch engine's options, the incremental
//! [`Session`](crate::incremental::Session), `AnalysisFingerprint` (which decides
//! "config changed → re-analyze everything"), and the result-cache key. Keeping
//! them aligned was a memory exercise, and it failed twice in ways users saw:
//!
//! * `laravelAliases` reached only the batch engine, so `--watch` produced
//!   `class.notFound` storms on every facade name a single-shot run resolved;
//! * the alias *source files* reached neither the fingerprint nor the cache key,
//!   so editing `config/app.php` served a stale cached report.
//!
//! Now there is one struct. Adding a field to [`AnalysisInputs`] is the only way
//! to add an analysis input, and [`AnalysisInputs::fingerprint`] destructures it
//! **exhaustively** — so the compiler routes you to the fingerprint, and from
//! there to the cache key and both engines.
//!
//! Discovery inputs (paths / exclude / extensions) deliberately live in
//! [`crate::incremental::DiscoveryFingerprint`] instead: they change the file
//! *set* and so require a full re-walk, whereas these change per-file *results*
//! and only require re-analysis. That split is why they are not merged here.

use php_config::{Config, RuleOptions};
use php_rules::{PhpVersion, Terminators};
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

/// The Laravel facade aliases in effect, plus the bytes they were derived from.
///
/// Carrying the source bytes is the point: the alias map is computed from files
/// *outside* the analyzed set (`config/app.php`, `vendor/composer/installed.json`),
/// so nothing else in the cache key or fingerprint would notice them changing.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LaravelAliasInputs {
    /// `alias name` → `target FQN`, in deterministic order.
    pub aliases: Vec<(String, String)>,
    /// `(path, contents)` of each alias source that existed, in read order.
    pub sources: Vec<(String, String)>,
}

/// Everything that can change the output of analysis, resolved.
///
/// Fields hold **post-override, post-file-load** values so both engines consume
/// byte-identical data rather than each re-deriving it from `Config`.
#[derive(Debug, Clone)]
pub struct AnalysisInputs {
    pub level: u8,
    pub php_version: PhpVersion,
    /// The raw config string, kept because the *unparsed* value is what the
    /// cache key hashed historically (`"8.1"` vs `"8.1.0"` differ textually but
    /// resolve alike; keeping it preserves the existing key).
    pub php_version_raw: Option<String>,
    pub treat_phpdoc_types_as_certain: bool,
    pub infer_untyped_signatures: bool,
    pub rule_options: RuleOptions,
    pub check_explicit_mixed: Option<bool>,
    pub check_implicit_mixed: Option<bool>,
    pub check_uninitialized_properties: bool,
    pub check_too_wide_return_public: bool,
    pub terminators: Arc<Terminators>,
    pub early_terminating_function_calls: Vec<String>,
    pub early_terminating_method_calls: BTreeMap<String, Vec<String>>,
    pub type_aliases: BTreeMap<String, String>,
    /// `None` when `laravelAliases` is off.
    pub laravel: Option<LaravelAliasInputs>,
}

impl AnalysisInputs {
    /// Resolve the analysis inputs for a run. The one constructor.
    pub fn resolve(config: &Config, root: &Path) -> Self {
        AnalysisInputs {
            level: config.level.value(),
            php_version: config
                .php_version
                .as_deref()
                .and_then(PhpVersion::parse)
                .unwrap_or_default(),
            php_version_raw: config.php_version.clone(),
            treat_phpdoc_types_as_certain: config.treat_phpdoc_types_as_certain,
            infer_untyped_signatures: config.infer_untyped_signatures,
            rule_options: config.rule_options(),
            check_explicit_mixed: config.check_explicit_mixed,
            check_implicit_mixed: config.check_implicit_mixed,
            check_uninitialized_properties: config.check_uninitialized_properties,
            check_too_wide_return_public: config.check_too_wide_return_public,
            terminators: Arc::new(Terminators {
                functions: config
                    .early_terminating_function_calls
                    .iter()
                    .map(|f| f.trim_start_matches('\\').to_ascii_lowercase())
                    .collect(),
                methods: config
                    .early_terminating_method_calls
                    .values()
                    .flatten()
                    .map(|m| m.to_ascii_lowercase())
                    .collect(),
            }),
            early_terminating_function_calls: config.early_terminating_function_calls.clone(),
            early_terminating_method_calls: config
                .early_terminating_method_calls
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            type_aliases: config
                .type_aliases
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            laravel: config
                .laravel_aliases
                .then(|| crate::laravel::alias_inputs(root)),
        }
    }

    /// Inputs with everything at its default, for callers that only vary a few
    /// knobs (the public `analyze_parsed` entry point and tests). Prefer
    /// [`Self::resolve`] whenever a `Config` is available.
    pub fn defaults_for(level: u8, php_version: PhpVersion) -> Self {
        AnalysisInputs {
            level,
            php_version,
            php_version_raw: None,
            treat_phpdoc_types_as_certain: true,
            infer_untyped_signatures: true,
            rule_options: php_config::Level(level).rule_options(),
            check_explicit_mixed: None,
            check_implicit_mixed: None,
            check_uninitialized_properties: false,
            check_too_wide_return_public: false,
            terminators: Arc::new(Terminators::default()),
            early_terminating_function_calls: Vec::new(),
            early_terminating_method_calls: BTreeMap::new(),
            type_aliases: BTreeMap::new(),
            laravel: None,
        }
    }

    /// The facade aliases to register, empty when the feature is off.
    pub fn facade_aliases(&self) -> &[(String, String)] {
        self.laravel.as_ref().map_or(&[], |l| l.aliases.as_slice())
    }

    /// Feed every analysis input into `h`.
    ///
    /// **Exhaustively destructured on purpose**: adding a field to
    /// [`AnalysisInputs`] without deciding how it is hashed is a compile error
    /// here, and this one function backs both the incremental fingerprint and
    /// the result-cache key. Never introduce `..` into this pattern.
    pub(crate) fn hash_into(&self, h: &mut crate::result_cache::StableHasher) {
        let AnalysisInputs {
            level,
            php_version,
            php_version_raw,
            treat_phpdoc_types_as_certain,
            infer_untyped_signatures,
            rule_options,
            check_explicit_mixed,
            check_implicit_mixed,
            check_uninitialized_properties,
            check_too_wide_return_public,
            // Derived from the two `early_terminating_*` lists below, so hashing
            // those covers it.
            terminators: _,
            early_terminating_function_calls,
            early_terminating_method_calls,
            type_aliases,
            laravel,
        } = self;

        h.write_u64(*level as u64);
        h.write_u64(php_version.id() as u64);
        h.write_opt_str(php_version_raw.as_deref());
        h.write_bool(*treat_phpdoc_types_as_certain);
        h.write_bool(*infer_untyped_signatures);
        h.write_bool(rule_options.report_maybes);
        h.write_bool(rule_options.check_nullables);
        h.write_bool(rule_options.check_explicit_mixed);
        h.write_bool(rule_options.check_implicit_mixed);
        h.write_bool(rule_options.check_uninitialized_properties);
        h.write_bool(rule_options.check_too_wide_return_public);
        h.write_opt_bool(*check_explicit_mixed);
        h.write_opt_bool(*check_implicit_mixed);
        h.write_bool(*check_uninitialized_properties);
        h.write_bool(*check_too_wide_return_public);
        for f in early_terminating_function_calls {
            h.write_str(f);
        }
        for (class, methods) in early_terminating_method_calls {
            h.write_str(class);
            for m in methods {
                h.write_str(m);
            }
        }
        for (name, body) in type_aliases {
            h.write_str(name);
            h.write_str(body);
        }
        // The alias map AND its sources: the sources live outside the analyzed
        // file set, so nothing else would notice them changing.
        h.write_bool(laravel.is_some());
        if let Some(l) = laravel {
            for (alias, target) in &l.aliases {
                h.write_str(alias);
                h.write_str(target);
            }
            for (path, contents) in &l.sources {
                h.write_str(path);
                h.write_bytes(contents.as_bytes());
            }
        }
    }

    /// The opaque fingerprint the incremental session compares between passes.
    ///
    /// Equality here means "no analysis input changed", so a pass may reuse
    /// per-file findings. Derived from [`Self::hash_into`] so it can never drift
    /// from the cache key.
    pub fn fingerprint(&self) -> String {
        let mut h = crate::result_cache::StableHasher::new();
        h.write_str("analysis-inputs-v1");
        self.hash_into(&mut h);
        h.finish_hex()
    }
}
