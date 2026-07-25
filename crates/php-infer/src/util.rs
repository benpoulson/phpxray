//! Small helpers shared by the inference (`lib.rs`) and flow (`flow.rs`) halves
//! of this crate.
//!
//! These existed as verbatim copies in both files. They are trivial enough that
//! duplication looked harmless, but one of them (`last_segment`) had already
//! grown a cosmetic difference between the copies — which is exactly how the
//! costly drifts start.

use php_types::Type;
use std::collections::HashMap;

/// What an untyped parameter falls back to when typing a body.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ParamFallback {
    /// Declaration-site: no call sites are in view, so an untyped parameter is
    /// `mixed` (`list<mixed>` when variadic).
    Declared,
    /// Body-seeding: use the observed call-site / callback argument types.
    Inferred,
}

/// The type a parameter has **inside** the function-like body.
///
/// The one answer to that question, shared by all five former seeders (three
/// over AST `Param`s in `lib.rs`/`flow.rs`, two over `ParamReflection` in
/// `type_map.rs`). They varied along exactly three axes, now explicit
/// arguments: `native` (native hints only vs PHPDoc-refined), `variadic`
/// wrapping, and the untyped `fallback` chain. Keeping them apart is what let
/// the closure-inference copy silently lose its native branch.
///
/// `declared` is the parameter's own type when it has one; `inferred` is the
/// observed argument types for this parameter onwards.
pub(crate) fn param_local_type(
    declared: Option<&Type>,
    variadic: bool,
    native: bool,
    inferred: &[Type],
    fallback: ParamFallback,
) -> Type {
    let untyped = || match fallback {
        ParamFallback::Declared => Type::Mixed,
        ParamFallback::Inferred => inferred.first().cloned().unwrap_or(Type::Mixed),
    };
    // Native mode: a variadic is PHP's own untyped `array`, never `list<T>`.
    if native {
        return match (declared, variadic) {
            (_, true) => Type::Array(None),
            (Some(t), false) => t.clone(),
            (None, false) => untyped(),
        };
    }
    match (declared, variadic) {
        (Some(t), true) => Type::List(Box::new(t.clone())),
        (Some(t), false) => t.clone(),
        (None, true) => {
            let item = match fallback {
                ParamFallback::Declared => Type::Mixed,
                ParamFallback::Inferred if inferred.is_empty() => Type::Mixed,
                ParamFallback::Inferred => Type::union(inferred.to_vec()),
            };
            Type::List(Box::new(item))
        }
        (None, false) => untyped(),
    }
}

/// Drop `$this` and every `this->…` member place from an environment.
///
/// A `static` closure/arrow fn has no `$this`, so its captured environment must
/// lose both the variable and any narrowed property places hanging off it.
pub(crate) fn strip_this_vars(vars: &mut HashMap<String, Type>) {
    vars.retain(|k, _| k != "this" && !k.starts_with("this->"));
}

/// Whether every argument is a plain positional one — no spread, no named
/// argument, no first-class-callable placeholder.
///
/// Positional analyses (callback seeding, arity-based specialization) can only
/// map arguments to parameters when this holds.
pub(crate) fn args_are_plain_positional(args: &[php_ast::Arg]) -> bool {
    args.iter().all(arg_is_plain_positional)
}

/// [`args_are_plain_positional`] for a single argument.
pub(crate) fn arg_is_plain_positional(a: &php_ast::Arg) -> bool {
    !a.spread && !a.placeholder && a.name.is_none()
}

/// The last `\`-separated segment of a (possibly qualified) name.
///
/// A leading `\` needs no special handling: the last segment of `\A\b` and
/// `A\b` is `b` either way. The two former copies differed only in whether they
/// trimmed it first — see `last_segment_ignores_a_leading_separator`.
pub(crate) fn last_segment(name: &str) -> &str {
    name.rsplit('\\').next().unwrap_or(name)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The two pre-consolidation copies of `last_segment` differed: one trimmed
    /// a leading `\` before splitting, the other did not. They are equivalent —
    /// trimming cannot change what follows the *last* separator — so the copies
    /// were merged into the simpler form. This pins that equivalence.
    #[test]
    fn last_segment_ignores_a_leading_separator() {
        fn trimming(name: &str) -> &str {
            name.trim_start_matches('\\')
                .rsplit('\\')
                .next()
                .unwrap_or(name)
        }
        for name in [
            "",
            "bar",
            "\\bar",
            "Foo\\bar",
            "\\Foo\\bar",
            "\\\\",
            "\\",
            "A\\B\\C",
            "\\A\\B\\C",
            "trailing\\",
        ] {
            assert_eq!(last_segment(name), trimming(name), "for {name:?}");
        }
        assert_eq!(last_segment("\\Foo\\bar"), "bar");
        assert_eq!(last_segment("bar"), "bar");
    }

    #[test]
    fn strip_this_vars_drops_this_and_its_places() {
        let mut vars: HashMap<String, Type> = [
            ("this".to_string(), Type::Mixed),
            ("this->p".to_string(), Type::Int),
            ("other".to_string(), Type::String),
            ("thistle".to_string(), Type::Bool),
        ]
        .into_iter()
        .collect();
        strip_this_vars(&mut vars);
        let mut left: Vec<&str> = vars.keys().map(String::as_str).collect();
        left.sort_unstable();
        assert_eq!(left, ["other", "thistle"]);
    }
}
