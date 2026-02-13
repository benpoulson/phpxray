//! String interning.
//!
//! PHP source repeats identifiers heavily (`$this`, `array`, common class and
//! method names). Interning each distinct string once and referring to it by a
//! 4-byte [`Symbol`] makes name comparisons `O(1)` integer compares — which the
//! later name-resolution and type phases lean on constantly.
//!
//! We intern *identifiers, variable names, and namespace segments*. We do **not**
//! intern literal contents (string/number literals): those are effectively
//! unbounded and rarely repeat, so they stay as `Span` + decoded value at the
//! call site.
//!
//! The implementation is deliberately tiny and single-threaded. If profiling
//! later demands a concurrent interner we can swap in `lasso`, but the public
//! `Symbol`/`Interner` surface is meant to stay stable.

use std::collections::HashMap;

/// An interned string, cheap to copy and compare.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// The raw index. Useful for stable ordering / debugging only.
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Symbol({})", self.0)
    }
}

/// An arena of interned strings. Resolve a [`Symbol`] back to its text with
/// [`Interner::resolve`].
#[derive(Default)]
pub struct Interner {
    map: HashMap<Box<str>, u32>,
    strings: Vec<Box<str>>,
}

impl Interner {
    pub fn new() -> Interner {
        Interner::default()
    }

    /// Intern `s`, returning a stable [`Symbol`]. Interning the same text twice
    /// yields the same symbol.
    pub fn intern(&mut self, s: &str) -> Symbol {
        // `HashMap<Box<str>, _>` can be queried by `&str` since `Box<str>:
        // Borrow<str>`, so the hot path allocates nothing on a cache hit.
        if let Some(&id) = self.map.get(s) {
            return Symbol(id);
        }
        let id = self.strings.len() as u32;
        let boxed: Box<str> = s.into();
        self.strings.push(boxed.clone());
        self.map.insert(boxed, id);
        Symbol(id)
    }

    /// Resolve a symbol previously produced by this interner.
    #[inline]
    pub fn resolve(&self, sym: Symbol) -> &str {
        &self.strings[sym.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.strings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns_and_resolves() {
        let mut i = Interner::new();
        let a = i.intern("array");
        let b = i.intern("array");
        let c = i.intern("string");
        assert_eq!(a, b, "same text must intern to same symbol");
        assert_ne!(a, c);
        assert_eq!(i.resolve(a), "array");
        assert_eq!(i.resolve(c), "string");
        assert_eq!(i.len(), 2);
    }
}
