//! Per-analysis **symbol-access recording** for incremental invalidation.
//!
//! While a single file is analyzed, every cross-file information channel flows
//! through `ProjectIndex`/`ReflectionIndex` lookups. Those crates call
//! [`note_surface`]/[`note_body`]/[`note_global`] at their lookup choke points;
//! the analysis driver brackets each file with [`start`]/[`finish`] and stores
//! the recorded set as that file's dependency fingerprint. When a file changes,
//! only files whose recorded set intersects the changed symbols re-analyze.
//!
//! Names are recorded as case-insensitive FNV-1a hashes (`u64`), not strings —
//! lookups are hot (type inference hammers `find_method`), and hash collisions
//! only ever cause a *spurious* re-analysis, never a missed one. The recorder
//! is a thread-local: per-file analysis is single-threaded within its rayon
//! task, so bracketing start/finish around one file's analysis is race-free.
//! When no recording is active (every non-incremental caller), `note_*` is a
//! thread-local flag check — effectively free.

use std::cell::RefCell;
use std::collections::HashSet;

/// The dependencies recorded for one analyzed file.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct RecordedDeps {
    /// Symbols whose *declared surface* (signature/members/hierarchy) was
    /// consulted: `class()`, `function()`, hierarchy walks, member lookups.
    pub surface: HashSet<u64>,
    /// Symbols whose *body* was consulted (interprocedural return inference,
    /// callback context diagnostics). A body-only edit invalidates these.
    pub body: HashSet<u64>,
    /// Whether a whole-index scan was consulted (e.g. "do any final concrete
    /// descendants implement this method?"). A file with a global dependency
    /// must re-analyze whenever *any* symbol's surface changes.
    pub global: bool,
}

thread_local! {
    static ACTIVE: RefCell<Option<RecordedDeps>> = const { RefCell::new(None) };
}

/// Begin recording on this thread. Any previous in-progress recording is
/// discarded (analysis drivers bracket strictly, so this only matters after a
/// panic unwound mid-file).
pub fn start() {
    ACTIVE.with(|a| *a.borrow_mut() = Some(RecordedDeps::default()));
}

/// Stop recording on this thread and return what was recorded. Returns an
/// empty set if recording was never started.
pub fn finish() -> RecordedDeps {
    ACTIVE.with(|a| a.borrow_mut().take().unwrap_or_default())
}

/// Record a surface-level lookup of `name` (case-insensitive).
#[inline]
pub fn note_surface(name: &str) {
    ACTIVE.with(|a| {
        if let Some(deps) = a.borrow_mut().as_mut() {
            deps.surface.insert(symbol_hash(name));
        }
    });
}

/// Record a body-level lookup of `name` (case-insensitive).
#[inline]
pub fn note_body(name: &str) {
    ACTIVE.with(|a| {
        if let Some(deps) = a.borrow_mut().as_mut() {
            deps.body.insert(symbol_hash(name));
        }
    });
}

/// Record a whole-index scan.
#[inline]
pub fn note_global() {
    ACTIVE.with(|a| {
        if let Some(deps) = a.borrow_mut().as_mut() {
            deps.global = true;
        }
    });
}

/// Case-insensitive FNV-1a over `name` with any leading `\` stripped, so the
/// same symbol hashes identically however it was written (`\App\Foo`, `app\foo`).
/// Constants are case-sensitive in PHP, but hashing them case-insensitively
/// only widens invalidation — always safe.
pub fn symbol_hash(name: &str) -> u64 {
    let bytes = name.as_bytes();
    let bytes = if bytes.first() == Some(&b'\\') {
        &bytes[1..]
    } else {
        bytes
    };
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= b.to_ascii_lowercase() as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_is_case_and_leading_slash_insensitive() {
        assert_eq!(symbol_hash("App\\Foo"), symbol_hash("\\app\\foo"));
        assert_eq!(symbol_hash("strlen"), symbol_hash("STRLEN"));
        assert_ne!(symbol_hash("App\\Foo"), symbol_hash("App\\Bar"));
    }

    #[test]
    fn recording_brackets_capture_lookups() {
        // Nothing recorded while inactive.
        note_surface("Quiet\\Class");
        assert_eq!(finish(), RecordedDeps::default());

        start();
        note_surface("App\\User");
        note_body("App\\Repo");
        let deps = finish();
        assert!(deps.surface.contains(&symbol_hash("app\\user")));
        assert!(deps.body.contains(&symbol_hash("App\\Repo")));
        assert!(!deps.global);

        // finish() cleared the recorder.
        note_surface("App\\User");
        assert_eq!(finish(), RecordedDeps::default());
    }

    #[test]
    fn global_scan_flag() {
        start();
        note_global();
        assert!(finish().global);
    }
}
