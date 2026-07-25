use crate::{Finding, Report};
use php_config::{Config, IgnoreEntry};
use php_diagnostics::Severity;
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
    inputs: &crate::inputs::AnalysisInputs,
    files: &[CacheFileInput<'_>],
) -> Option<String> {
    let mut h = StableHasher::new();
    h.write_str("result-cache-v1");
    h.write_u64(SCHEMA_VERSION as u64);
    h.write_str(env!("CARGO_PKG_VERSION"));
    // The package version never changes between dev builds, so also key on the
    // running binary itself (size + mtime): an analyzer upgrade or rebuild must
    // never serve results computed by older rule/inference code.
    //
    // **Fail closed.** If the binary's identity is unavailable we cannot tell a
    // rebuilt analyzer from the one that wrote an entry, so the cache is
    // disabled for the run rather than keyed on a silently weaker digest.
    let meta = std::env::current_exe().and_then(std::fs::metadata).ok()?;
    h.write_u64(meta.len());
    let modified = meta
        .modified()
        .map(|m| m.duration_since(std::time::UNIX_EPOCH).unwrap_or_default())
        .ok()?;
    h.write_u64(modified.as_secs());
    // Every analysis input, hashed by the single registration point — so the
    // cache key can no longer omit one (it used to miss the Laravel alias
    // sources entirely, serving stale reports after a `config/app.php` edit).
    inputs.hash_into(&mut h);
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
    Some(h.finish_hex())
}

pub(crate) fn load(cache_dir: &Path, key: &str, echo: &CacheEcho) -> Option<Report> {
    let bytes = fs::read(cache_path(cache_dir, key)).ok()?;
    let cached: CachedReport = serde_json::from_slice(&bytes).ok()?;
    if cached.schema_version != SCHEMA_VERSION {
        return None;
    }
    // Second factor: a 64-bit key collision would also have to match these.
    if &cached.echo != echo {
        return None;
    }
    Some(Report {
        findings: cached.findings.into_iter().map(Into::into).collect(),
        files_analyzed: cached.files_analyzed,
        files_scanned: cached.files_scanned,
        timings: None,
    })
}

/// How many cache entries to keep. The cache is keyed on file *contents*, so
/// every edit mints a new entry; without a cap `results-v1/` grows without bound.
const MAX_ENTRIES: usize = 20;

pub(crate) fn store(cache_dir: &Path, key: &str, report: &Report, echo: CacheEcho) {
    let _ = fs::create_dir_all(cache_dir);
    let mut cached = CachedReport::from(report);
    cached.echo = echo;
    let Ok(bytes) = serde_json::to_vec(&cached) else {
        return;
    };
    let _ = fs::write(cache_path(cache_dir, key), bytes);
    evict_old_entries(cache_dir);
}

/// Keep only the newest [`MAX_ENTRIES`] entries, by mtime.
fn evict_old_entries(cache_dir: &Path) {
    let Ok(entries) = fs::read_dir(cache_dir) else {
        return;
    };
    let mut found: Vec<(std::time::SystemTime, PathBuf)> = entries
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().and_then(|x| x.to_str()) == Some(CACHE_FILE_EXT))
        .filter_map(|e| {
            let modified = e.metadata().and_then(|m| m.modified()).ok()?;
            Some((modified, e.path()))
        })
        .collect();
    if found.len() <= MAX_ENTRIES {
        return;
    }
    // Newest first, then drop the tail.
    found.sort_unstable_by_key(|(modified, _)| std::cmp::Reverse(*modified));
    for (_, path) in &found[MAX_ENTRIES..] {
        let _ = fs::remove_file(path);
    }
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

/// Intern a rule identifier to `&'static str`.
///
/// [`Finding::identifier`](crate::Finding) is `Option<&'static str>` because rules
/// return compile-time literals. Cache entries arrive as owned `String`s, so
/// loading used to `Box::leak` **every identifier of every finding on every
/// load** — unbounded growth proportional to findings × loads in a long-lived
/// process. Identifiers are a small closed set (a few hundred), so interning
/// leaks at most once per distinct identifier for the life of the process.
fn intern_identifier(id: &str) -> &'static str {
    use std::collections::HashSet;
    use std::sync::{Mutex, OnceLock};
    static INTERNED: OnceLock<Mutex<HashSet<&'static str>>> = OnceLock::new();
    let set = INTERNED.get_or_init(|| Mutex::new(HashSet::new()));
    let mut set = match set.lock() {
        Ok(g) => g,
        // A poisoned lock must not take down analysis; fall back to a leak.
        Err(_) => return Box::leak(id.to_string().into_boxed_str()),
    };
    if let Some(existing) = set.get(id) {
        return existing;
    }
    let leaked: &'static str = Box::leak(id.to_string().into_boxed_str());
    set.insert(leaked);
    leaked
}

/// Identifying facts echoed into each cache entry and re-checked on load.
#[derive(Serialize, Deserialize, Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CacheEcho {
    pub(crate) level: u8,
    pub(crate) files: usize,
    /// The project root, so a cache directory shared between projects (e.g. an
    /// explicit `--cache-dir`) cannot cross-serve on a key collision.
    pub(crate) root: String,
}

#[derive(Serialize, Deserialize)]
struct CachedReport {
    schema_version: u32,
    /// A cheap second factor against a 64-bit key collision: re-checked on load,
    /// so a colliding key still has to agree on the level and file counts.
    #[serde(default)]
    echo: CacheEcho,
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
            echo: CacheEcho::default(),
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
            identifier: finding.identifier.as_deref().map(intern_identifier),
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

pub(crate) struct StableHasher {
    hash: u64,
}

impl StableHasher {
    pub(crate) fn new() -> Self {
        Self {
            hash: 0xcbf2_9ce4_8422_2325,
        }
    }

    pub(crate) fn write_bool(&mut self, value: bool) {
        self.write_bytes(&[u8::from(value)]);
    }

    pub(crate) fn write_u64(&mut self, value: u64) {
        self.write_bytes(&value.to_le_bytes());
    }

    pub(crate) fn write_opt_bool(&mut self, value: Option<bool>) {
        match value {
            Some(v) => {
                self.write_bool(true);
                self.write_bool(v);
            }
            None => self.write_bool(false),
        }
    }

    pub(crate) fn write_opt_str(&mut self, value: Option<&str>) {
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

    pub(crate) fn write_str(&mut self, value: &str) {
        self.write_bytes(value.as_bytes());
    }

    pub(crate) fn write_bytes(&mut self, bytes: &[u8]) {
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

    pub(crate) fn finish_hex(self) -> String {
        format!("{:016x}", self.hash)
    }
}

#[cfg(test)]
mod intern_tests {
    use super::intern_identifier;

    /// The same identifier must intern to the same pointer, so repeated cache
    /// loads stop leaking a fresh copy each time.
    #[test]
    fn identifiers_intern_to_one_allocation() {
        let a = intern_identifier("return.type");
        let b = intern_identifier(&String::from("return.type"));
        assert!(std::ptr::eq(a, b), "identifier was leaked twice");
        assert_eq!(a, "return.type");
        assert!(!std::ptr::eq(a, intern_identifier("argument.type")));
    }
}
