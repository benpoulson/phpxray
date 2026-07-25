//! Source positions for the PHP analyzer.
//!
//! This is the foundation crate: it has zero dependencies and is depended on by
//! essentially everything (lexer, AST, diagnostics, and later name-resolution
//! and the type system). Keeping it dependency-free means changes here never
//! trigger wide rebuilds.
//!
//! Positions are stored as **byte offsets** (`u32`). No PHP source file is
//! anywhere near 4 GiB, so `u32` halves the size of every [`Span`] versus
//! `usize` — and every AST node carries one. Human-facing line/column pairs are
//! derived on demand via [`LineIndex`], never stored on nodes.

/// A half-open byte range `[start, end)` into a source string.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const DUMMY: Span = Span { start: 0, end: 0 };

    #[inline]
    pub fn new(start: u32, end: u32) -> Span {
        debug_assert!(start <= end, "span start must not exceed end");
        Span { start, end }
    }

    /// Build a span from `usize` offsets (e.g. slice indices), truncating to
    /// `u32`. Callers are expected to operate on sub-4-GiB sources.
    #[inline]
    pub fn from_range(range: std::ops::Range<usize>) -> Span {
        Span::new(range.start as u32, range.end as u32)
    }

    /// An empty span at a single offset (used for synthesized / error nodes).
    #[inline]
    pub fn at(offset: u32) -> Span {
        Span {
            start: offset,
            end: offset,
        }
    }

    #[inline]
    pub fn len(self) -> u32 {
        self.end - self.start
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    #[inline]
    pub fn contains(self, offset: u32) -> bool {
        self.start <= offset && offset < self.end
    }

    /// The smallest span covering both `self` and `other`.
    #[inline]
    pub fn to(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    #[inline]
    pub fn range(self) -> std::ops::Range<usize> {
        self.start as usize..self.end as usize
    }

    /// Slice the source text this span refers to. The caller must pass the same
    /// source the span was created against.
    #[inline]
    pub fn text(self, source: &str) -> &str {
        &source[self.range()]
    }
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Compact form keeps AST snapshots readable: `0..5`.
        write!(f, "{}..{}", self.start, self.end)
    }
}

/// A stable identity for an AST node, used as the key of node-indexed maps
/// (notably `php_infer`'s type map).
///
/// Today this **is** the node's byte span, which is why it exists as a newtype
/// rather than a bare `(u32, u32)`: the planned arena migration (CLAUDE.md §10.4)
/// replaces span-derived identity with a real node ID, and the intent is that
/// only this type's definition and constructor change, not every call site.
///
/// # Known identity flaws inherited from spans
///
/// These are properties of *span* identity, not bugs in this type. The arena
/// migration removes them; until then callers must be aware:
///
/// * **Identical-span parent/child pairs collide** — a wrapper node that
///   consumes no extra source text shares its child's span, so whichever is
///   recorded last wins. `php-ast` documents a no-identical-spans invariant for
///   the parser to uphold; violations are bugs against it.
/// * **Loop fixpoint iterations overwrite** — a body re-analysed per iteration
///   records the same keys each round, so the last iteration's types survive.
/// * **Re-seeded callback bodies need a separate map** — recording one body under
///   two different parameter seedings would collide, which is why
///   `contextual_body_type_map` builds a parallel map instead of merging.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct NodeKey(u32, u32);

impl NodeKey {
    /// The key identifying the node that occupies `span`.
    #[inline]
    pub fn of(span: Span) -> Self {
        NodeKey(span.start, span.end)
    }

    /// The raw span bounds. For diagnostics/tests only — do not key new maps on
    /// the tuple, key them on `NodeKey`.
    #[inline]
    pub fn bounds(self) -> (u32, u32) {
        (self.0, self.1)
    }
}

/// A 1-based line and column (column counted in bytes within the line).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

/// Precomputed line-start offsets for one source string, enabling
/// `offset -> (line, col)` lookups in `O(log lines)`.
///
/// Built once per file when diagnostics need to be rendered; never stored on
/// AST nodes.
#[derive(Clone, Debug)]
pub struct LineIndex {
    /// Byte offset of the first character of each line. `line_starts[0] == 0`.
    line_starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(source: &str) -> LineIndex {
        let mut line_starts = Vec::with_capacity(source.len() / 24 + 1);
        line_starts.push(0);
        for (i, b) in source.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i as u32 + 1);
            }
        }
        LineIndex { line_starts }
    }

    /// Convert a byte offset to a 1-based line/column.
    pub fn line_col(&self, offset: u32) -> LineCol {
        // Largest line_start <= offset.
        let line = match self.line_starts.binary_search(&offset) {
            Ok(exact) => exact,
            Err(next) => next - 1,
        };
        let col = offset - self.line_starts[line];
        LineCol {
            line: line as u32 + 1,
            col: col + 1,
        }
    }

    /// Total number of lines.
    pub fn line_count(&self) -> u32 {
        self.line_starts.len() as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn span_basics() {
        let s = Span::new(2, 7);
        assert_eq!(s.len(), 5);
        assert!(!s.is_empty());
        assert!(s.contains(2) && s.contains(6) && !s.contains(7));
        assert_eq!(s.text("0123456789"), "23456");
        assert_eq!(format!("{s:?}"), "2..7");
    }

    #[test]
    fn span_merge() {
        assert_eq!(Span::new(1, 3).to(Span::new(5, 8)), Span::new(1, 8));
        assert_eq!(Span::new(5, 8).to(Span::new(1, 3)), Span::new(1, 8));
    }

    #[test]
    fn line_index_maps_offsets() {
        // "ab\ncde\nf"  offsets: a0 b1 \n2 c3 d4 e5 \n6 f7
        let idx = LineIndex::new("ab\ncde\nf");
        assert_eq!(idx.line_count(), 3);
        assert_eq!(idx.line_col(0), LineCol { line: 1, col: 1 });
        assert_eq!(idx.line_col(1), LineCol { line: 1, col: 2 });
        assert_eq!(idx.line_col(3), LineCol { line: 2, col: 1 });
        assert_eq!(idx.line_col(5), LineCol { line: 2, col: 3 });
        assert_eq!(idx.line_col(7), LineCol { line: 3, col: 1 });
    }
}
