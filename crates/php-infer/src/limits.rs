//! The bounds that keep inference terminating and its types small enough to be
//! useful.
//!
//! These were scattered across four modules as local `const`s and, twice, as a
//! bare literal — so it was impossible to see the set of things that trade
//! precision for termination, or to tell which numbers were related. Every one
//! is a deliberate approximation: exceeding a bound widens toward `mixed` rather
//! than looping or carrying an unbounded type.

/// How many times a loop body is re-analysed before its environment is accepted.
///
/// Loop types are computed by bounded fixpoint: each round feeds the merged
/// environment back in. Convergence is usually immediate; this caps pathological
/// cases (nested loops mutating the same shape), after which types widen.
pub(crate) const LOOP_FIXPOINT_LIMIT: usize = 6;

/// Union arms tolerated on a variable carried around a loop before widening.
///
/// A variable reassigned to a new literal each iteration would otherwise grow an
/// arm per round. On the first breach, literals generalize to their base types;
/// if it *still* exceeds the cap the type becomes `mixed`.
pub(crate) const LOOP_UNION_ARM_CAP: usize = 8;

/// Distinct array shapes tolerated in one union before collapsing them.
///
/// Branch-merged index writes produce a shape per path, so this bounds an
/// exponential blow-up in code with many sequential conditionals.
pub(crate) const SHAPE_UNION_ARM_CAP: usize = 6;

/// Fields a single array literal may have before its type stops being a shape.
///
/// A large literal table (a lookup map, a fixture) is far more useful typed as
/// `array<K, V>` than as a hundred-field shape nobody will read.
pub(crate) const MAX_SHAPE_FIELDS: usize = 64;

/// Longest string literal kept as a `LiteralString` type.
///
/// Literal string types make constant comparisons and literal-union parameters
/// work; beyond this length the precision stops paying for carrying the bytes
/// around, and the type degrades to `string`.
pub(crate) const MAX_LITERAL_STRING: usize = 64;

/// Longest result of constant-folding string concatenation or repetition.
///
/// Bounds `'a' . 'b'` and `str_repeat('x', $n)` folding so a generated blob
/// cannot be materialized as a type. Both folding sites share this cap.
pub(crate) const FOLD_CAP: usize = 512;

/// Interprocedural analysis depth.
///
/// Inference may step into a callee's body to refine its return type, but only
/// one level: a callee is analysed at depth 1 ([`crate::signatures`] seeds it
/// there), and [`crate::returns`] refuses to refine once `depth >= 2`. The two
/// numbers are the same bound seen from either end — raising one without the
/// other silently disables refinement rather than deepening it.
pub(crate) const CALLEE_ANALYSIS_DEPTH: u32 = 1;

/// The depth at which return refinement stops. See [`CALLEE_ANALYSIS_DEPTH`].
pub(crate) const MAX_REFINE_DEPTH: u32 = CALLEE_ANALYSIS_DEPTH + 1;

/// Whole-project signature-inference fixpoint rounds.
///
/// Each round lets an inferred return feed the next (`h()` returning `g()`
/// returning a literal needs two). Converges earlier when nothing changes.
pub(crate) const SIGNATURE_INFERENCE_ROUNDS: u32 = 3;
