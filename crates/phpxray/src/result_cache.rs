use crate::{Finding, Report};
use php_config::{Config, IgnoreEntry, RuleOptions};
use php_diagnostics::Severity;
use php_rules::PhpVersion;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};

const SCHEMA_VERSION: u32 = 1;
const CACHE_FILE_EXT: &str = "json";

pub(crate) struct CacheFileInput<'a> {
    pub(crate) path: &'a str,
    pub(crate) source: &'a str,
    pub(crate) analyze: bool,
}

pub(crate) fn default_cache_dir(root: &Path) -> PathBuf {
    root.join(".phpxray").join("cache").join("results-v1")
}

pub(crate) fn key(
    config: &Config,
    root: &Path,
    php_version: PhpVersion,
    rule_options: RuleOptions,
    files: &[CacheFileInput<'_>],
) -> String {
    let mut h = StableHasher::new();
    h.write_str("result-cache-v1");
    h.write_u64(SCHEMA_VERSION as u64);
    h.write_str(env!("CARGO_PKG_VERSION"));
    // The package version never changes between dev builds, so also key on the
    // running binary itself (size + mtime): an analyzer upgrade or rebuild must
    // never serve results computed by older rule/inference code.
    if let Ok(meta) = std::env::current_exe().and_then(std::fs::metadata) {
        h.write_u64(meta.len());
        if let Ok(d) = meta
            .modified()
            .map(|m| m.duration_since(std::time::UNIX_EPOCH).unwrap_or_default())
        {
            h.write_u64(d.as_secs());
        }
    }
    h.write_u64(php_version.id() as u64);
    h.write_u64(config.level.value() as u64);
    h.write_bool(rule_options.report_maybes);
    h.write_bool(rule_options.check_nullables);
    h.write_bool(rule_options.check_explicit_mixed);
    h.write_bool(rule_options.check_implicit_mixed);
    h.write_bool(rule_options.check_uninitialized_properties);
    h.write_bool(rule_options.check_too_wide_return_public);
    h.write_bool(config.treat_phpdoc_types_as_certain);
    h.write_bool(config.infer_untyped_signatures);
    h.write_bool(config.laravel_aliases);
    for f in &config.early_terminating_function_calls {
        h.write_str(f);
    }
    for (class, methods) in {
        let mut entries: Vec<_> = config.early_terminating_method_calls.iter().collect();
        entries.sort();
        entries
    } {
        h.write_str(class);
        for m in methods {
            h.write_str(m);
        }
    }
    for (name, body) in {
        let mut entries: Vec<_> = config.type_aliases.iter().collect();
        entries.sort();
        entries
    } {
        h.write_str(name);
        h.write_str(body);
    }
    h.write_bool(config.report_unmatched_ignored);
    write_config_paths(&mut h, config);
    write_ignore_entries(&mut h, &config.ignore);
    write_baseline(&mut h, config, root);
    h.write_u64(files.len() as u64);
    for file in files {
        h.write_str(file.path);
        h.write_bool(file.analyze);
        h.write_bytes(file.source.as_bytes());
    }
    h.finish_hex()
}

pub(crate) fn load(cache_dir: &Path, key: &str) -> Option<Report> {
    let bytes = fs::read(cache_path(cache_dir, key)).ok()?;
    let cached: CachedReport = serde_json::from_slice(&bytes).ok()?;
    if cached.schema_version != SCHEMA_VERSION {
        return None;
    }
    Some(Report {
        findings: cached.findings.into_iter().map(Into::into).collect(),
        files_analyzed: cached.files_analyzed,
        files_scanned: cached.files_scanned,
        timings: None,
    })
}

pub(crate) fn store(cache_dir: &Path, key: &str, report: &Report) {
    let _ = fs::create_dir_all(cache_dir);
    let Ok(bytes) = serde_json::to_vec(&CachedReport::from(report)) else {
        return;
    };
    let _ = fs::write(cache_path(cache_dir, key), bytes);
}

fn cache_path(cache_dir: &Path, key: &str) -> PathBuf {
    cache_dir.join(format!("{key}.{CACHE_FILE_EXT}"))
}

fn write_config_paths(h: &mut StableHasher, config: &Config) {
    h.write_strs(&config.paths);
    h.write_strs(&config.scan_paths);
    h.write_strs(&config.scan_files);
    h.write_strs(&config.exclude);
    h.write_strs(&config.exclude_paths.analyse);
    h.write_strs(&config.exclude_paths.analyse_and_scan);
    h.write_strs(&config.extensions);
    h.write_opt_str(config.php_version.as_deref());
    h.write_opt_str(config.baseline.as_deref());
}

fn write_ignore_entries(h: &mut StableHasher, entries: &[IgnoreEntry]) {
    h.write_u64(entries.len() as u64);
    for entry in entries {
        h.write_opt_str(entry.message.as_deref());
        h.write_opt_str(entry.identifier.as_deref());
        h.write_opt_str(entry.path.as_deref());
        h.write_strs(&entry.paths);
        match entry.count {
            Some(count) => {
                h.write_bool(true);
                h.write_u64(count as u64);
            }
            None => h.write_bool(false),
        }
    }
}

fn write_baseline(h: &mut StableHasher, config: &Config, root: &Path) {
    let Some(path) = &config.baseline else {
        h.write_bool(false);
        return;
    };
    h.write_bool(true);
    h.write_str(path);
    match fs::read(root.join(path)) {
        Ok(bytes) => {
            h.write_str("ok");
            h.write_bytes(&bytes);
        }
        Err(err) => {
            h.write_str("err");
            h.write_str(&format!("{:?}", err.kind()));
        }
    }
}

#[derive(Serialize, Deserialize)]
struct CachedReport {
    schema_version: u32,
    files_analyzed: usize,
    // Older cache entries predate this field; the binary-identity cache key
    // makes that unreachable in practice, but stay lenient anyway.
    #[serde(default)]
    files_scanned: usize,
    findings: Vec<CachedFinding>,
}

impl From<&Report> for CachedReport {
    fn from(report: &Report) -> Self {
        Self {
            schema_version: SCHEMA_VERSION,
            files_analyzed: report.files_analyzed,
            files_scanned: report.files_scanned,
            findings: report.findings.iter().map(CachedFinding::from).collect(),
        }
    }
}

#[derive(Serialize, Deserialize)]
struct CachedFinding {
    path: String,
    line: u32,
    column: u32,
    message: String,
    identifier: Option<String>,
    severity: CachedSeverity,
}

impl From<&Finding> for CachedFinding {
    fn from(finding: &Finding) -> Self {
        Self {
            path: finding.path.clone(),
            line: finding.line,
            column: finding.column,
            message: finding.message.clone(),
            identifier: finding.identifier.map(str::to_string),
            severity: finding.severity.into(),
            // Fixes are never cached: `--fix` runs bypass the result cache.
        }
    }
}

impl From<CachedFinding> for Finding {
    fn from(finding: CachedFinding) -> Self {
        Self {
            path: finding.path,
            line: finding.line,
            column: finding.column,
            message: finding.message,
            identifier: finding
                .identifier
                .map(|id| Box::leak(id.into_boxed_str()) as &'static str),
            severity: finding.severity.into(),
            fix: None,
        }
    }
}

#[derive(Serialize, Deserialize)]
enum CachedSeverity {
    Error,
    Warning,
}

impl From<Severity> for CachedSeverity {
    fn from(severity: Severity) -> Self {
        match severity {
            Severity::Error => Self::Error,
            Severity::Warning => Self::Warning,
        }
    }
}

impl From<CachedSeverity> for Severity {
    fn from(severity: CachedSeverity) -> Self {
        match severity {
            CachedSeverity::Error => Severity::Error,
            CachedSeverity::Warning => Severity::Warning,
        }
    }
}

struct StableHasher {
    hash: u64,
}

impl StableHasher {
    fn new() -> Self {
        Self {
            hash: 0xcbf2_9ce4_8422_2325,
        }
    }

    fn write_bool(&mut self, value: bool) {
        self.write_bytes(&[u8::from(value)]);
    }

    fn write_u64(&mut self, value: u64) {
        self.write_bytes(&value.to_le_bytes());
    }

    fn write_opt_str(&mut self, value: Option<&str>) {
        match value {
            Some(value) => {
                self.write_bool(true);
                self.write_str(value);
            }
            None => self.write_bool(false),
        }
    }

    fn write_strs(&mut self, values: &[String]) {
        self.write_u64(values.len() as u64);
        for value in values {
            self.write_str(value);
        }
    }

    fn write_str(&mut self, value: &str) {
        self.write_bytes(value.as_bytes());
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        self.write_u64_raw(bytes.len() as u64);
        for byte in bytes {
            self.hash ^= u64::from(*byte);
            self.hash = self.hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }

    fn write_u64_raw(&mut self, value: u64) {
        for byte in value.to_le_bytes() {
            self.hash ^= u64::from(byte);
            self.hash = self.hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }

    fn finish_hex(self) -> String {
        format!("{:016x}", self.hash)
    }
}
