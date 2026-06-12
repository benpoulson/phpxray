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
//! The implementation is backed by `lasso::ThreadedRodeo`, a concurrent interner:
//! [`Interner::intern`] takes `&self`, so many threads can intern into one shared
//! interner at once (the parser parallelises file parsing over a single
//! project-wide interner). Reads ([`Interner::resolve`]) are lock-free, keeping
//! the analysis hot path — which only ever resolves — as cheap as before. The
//! public `Symbol`/`Interner` surface is unchanged except that `intern` no longer
//! needs `&mut`.

use lasso::{Key, Spur, ThreadedRodeo};

/// An interned string, cheap to copy and compare.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// The raw index. Useful for stable ordering / debugging only.
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.0
    }

    #[inline]
    fn from_spur(spur: Spur) -> Symbol {
        // `Spur::into_usize` is the 0-based insertion index; it always fits u32
        // (no PHP project has 4 billion distinct identifiers).
        Symbol(spur.into_usize() as u32)
    }

    #[inline]
    fn to_spur(self) -> Spur {
        Spur::try_from_usize(self.0 as usize).expect("valid symbol index")
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Symbol({})", self.0)
    }
}

/// A concurrent arena of interned strings. Resolve a [`Symbol`] back to its text
/// with [`Interner::resolve`].
#[derive(Default)]
pub struct Interner {
    rodeo: ThreadedRodeo,
}

impl Interner {
    pub fn new() -> Interner {
        Interner::default()
    }

    /// Intern `s`, returning a stable [`Symbol`]. Interning the same text twice
    /// — from any thread — yields the same symbol.
    #[inline]
    pub fn intern(&self, s: &str) -> Symbol {
        Symbol::from_spur(self.rodeo.get_or_intern(s))
    }

    /// Resolve a symbol previously produced by this interner.
    #[inline]
    pub fn resolve(&self, sym: Symbol) -> &str {
        self.rodeo.resolve(&sym.to_spur())
    }

    pub fn len(&self) -> usize {
        self.rodeo.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rodeo.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns_and_resolves() {
        let i = Interner::new();
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
