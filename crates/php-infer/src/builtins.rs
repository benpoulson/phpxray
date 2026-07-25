//! Built-in function knowledge: **the** place that knows what individual PHP
//! built-ins mean to inference.
//!
//! This knowledge used to be scattered as string-literal matches across
//! `php-infer` and `php-rules` — `"array_map"` alone appeared in six files
//! across three crates — with the guard against userland functions *shadowing* a
//! builtin name applied at some sites and not others. Keeping the name list, the
//! capability it implies, and the shadowing guard in one module is what stops
//! those from drifting apart.
//!
//! Return specializations stay expressed as code (they are value-dependent, not
//! table-shaped), but they live here and are reached from one dispatch point.

use crate::limits::FOLD_CAP;
use crate::{
    args_are_plain_positional, arrays, ascii_change_first, last_segment,
    template_observation_is_imprecise, TypeCtx,
};
use php_ast::{Arg, ExprKind, Name};
use php_types::Type;

/// Built-ins that can introduce or read variables the analyzer cannot see, so a
/// scope containing one is not safely analyzable for definedness.
///
/// A call to any of these makes [`crate::definedness`] bail out of the whole
/// scope rather than report a possibly-undefined variable it might have created.
const VARIABLE_ESCAPE_FUNCTIONS: &[&str] = &[
    "extract",
    "parse_str",
    "mb_parse_str",
    "get_defined_vars",
    "compact",
    "eval",
];

/// Whether `lowercased_name` defeats definedness analysis for its whole scope.
pub(crate) fn is_variable_escape_fn(lowercased_name: &str) -> bool {
    VARIABLE_ESCAPE_FUNCTIONS.contains(&lowercased_name)
}

/// Built-in functions known to be pure / side-effect-free.
///
/// A conservative subset of phpstan's `@phpstan-pure` stub annotations — chosen so
/// a statement-level call to one is unambiguously a mistake. Functions whose
/// purity is version- or argument-dependent are intentionally omitted.
const PURE_BUILTINS: &[&str] = &[
    "strlen",
    "count",
    "sizeof",
    "array_keys",
    "array_values",
    "array_merge",
    "array_map",
    "array_filter",
    "array_search",
    "in_array",
    "array_key_exists",
    "implode",
    "explode",
    "str_repeat",
    "str_replace",
    "substr",
    "strpos",
    "stripos",
    "strrpos",
    "trim",
    "ltrim",
    "rtrim",
    "strtolower",
    "strtoupper",
    "ucfirst",
    "ucwords",
    "lcfirst",
    "sprintf",
    "number_format",
    "abs",
    "ceil",
    "floor",
    "round",
    "max",
    "min",
    "intval",
    "floatval",
    "strval",
    "boolval",
    "is_int",
    "is_string",
    "is_array",
    "is_bool",
    "is_float",
    "is_null",
    "is_numeric",
    "is_object",
    "is_callable",
    "gettype",
    "json_encode",
    "base64_encode",
    "base64_decode",
    "urlencode",
    "urldecode",
    "htmlspecialchars",
    "htmlentities",
    "nl2br",
    "wordwrap",
    "str_pad",
    "str_split",
    "array_slice",
    "array_reverse",
    "array_unique",
    "array_flip",
    "array_sum",
    "array_product",
    "array_column",
    "array_combine",
    "array_fill",
    "array_pad",
    "range",
    "compact",
];

/// Whether calling `lowercased_name` and discarding the result is pointless.
pub fn is_pure_builtin(lowercased_name: &str) -> bool {
    PURE_BUILTINS.contains(&lowercased_name)
}

/// Which argument of a built-in takes a callable, and how that callable's
/// parameters are seeded from the other arguments.
///
/// The *data* lives here once; each consumer computes the actual types in its own
/// idiom (inference walks a [`TypeCtx`], the rules layer reads a type map), which
/// is why this is a shape description rather than a closure.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CallbackSpec {
    /// Index of the callable argument.
    pub callback: usize,
    /// How to seed the callable's parameters.
    pub seed: CallbackSeed,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CallbackSeed {
    /// One parameter per array argument *after* the callback (`array_map`).
    ArrayValuesAfterCallback,
    /// Value, and key too under `ARRAY_FILTER_USE_*` (`array_filter`).
    FilterOverArray0,
    /// Value, key, then the optional extra argument (`array_walk`).
    WalkOverArray0,
    /// Two values from the array being sorted (`usort`/`uasort`).
    ValuePairOfArray0,
    /// Two keys from the array being sorted (`uksort`).
    KeyPairOfArray0,
    /// The match array (`preg_replace_callback`).
    PregMatchArray,
}

/// The callback specification for a built-in, by lowercased global name.
///
/// Consulted by both the inference recorder and the rules layer's callback-context
/// pass, which previously kept separate copies of this list.
pub fn callback_spec(lowercased_name: &str) -> Option<CallbackSpec> {
    use CallbackSeed::*;
    let (callback, seed) = match lowercased_name {
        "array_map" => (0, ArrayValuesAfterCallback),
        "array_filter" => (1, FilterOverArray0),
        "array_walk" => (1, WalkOverArray0),
        "usort" | "uasort" => (1, ValuePairOfArray0),
        "uksort" => (1, KeyPairOfArray0),
        "preg_replace_callback" => (1, PregMatchArray),
        _ => return None,
    };
    Some(CallbackSpec { callback, seed })
}

impl TypeCtx<'_> {
    /// Does a call through `n` reach the **global built-in** of that name?
    ///
    /// The single shadowing guard. Every consumer of built-in knowledge in this
    /// module must pass through it, because PHP's unqualified-function fallback
    /// means a namespaced `function is_int(): bool` shadows the global one for
    /// unqualified calls in that namespace — with entirely different semantics.
    /// Narrowing on a shadow would be unsound (over-narrowing is never allowed);
    /// specializing its return would be simply wrong. A fully-qualified
    /// `\is_int` always reaches the built-in.
    ///
    /// A name that resolves to nothing stays permissive: an incomplete index must
    /// not silently switch built-in knowledge off across a whole project.
    /// Resolution goes through `php_resolve`'s fallback logic rather than
    /// reimplementing it.
    pub(crate) fn resolves_to_builtin(&self, n: &Name) -> bool {
        !self.function_reflection(n).is_some_and(|f| !f.builtin)
    }

    /// Argument-dependent return types for selected built-ins. Returns `None` to
    /// fall back to the stub signature.
    pub(crate) fn dynamic_return(&self, fname: &str, args: &[php_ast::Arg]) -> Option<Type> {
        if !args_are_plain_positional(args) {
            return None;
        }

        // The string-replace family returns the *subject*'s shape: a string
        // subject yields a string, an array subject an array. The stub can only
        // say `string|array`, which then poisons every downstream string use.
        if let Some(idx) = match fname {
            "str_replace"
            | "str_ireplace"
            | "preg_replace"
            | "preg_replace_callback"
            | "preg_replace_callback_array" => Some(2),
            "substr_replace" => Some(0),
            _ => None,
        } {
            return match self.infer(&args.get(idx)?.value) {
                Type::String | Type::StringOf(_) | Type::LiteralString(_) => Some(Type::String),
                Type::Array(_) | Type::List(_) => Some(Type::Array(None)),
                _ => None,
            };
        }

        if let Some(t) = self.string_builtin_return(fname, args) {
            return Some(t);
        }

        // `count()` of a non-empty container is at least 1.
        if matches!(fname, "count" | "sizeof") {
            if let Type::NonEmpty(_) = self.infer(&args.first()?.value) {
                return Some(Type::int_range(Some(1), None));
            }
            return None;
        }

        // Array functions that preserve their first argument's element type — the
        // stubs return a bare `array`, losing the value type and cascading into
        // downstream `array<K,V>` argument/return mismatches.
        match fname {
            "array_map" => self.array_map_return(args),
            // `array_merge(...$arrays)` unions element types; all-list inputs
            // stay a list (re-indexed), and one non-empty input makes the
            // result non-empty.
            "array_merge" => {
                if args.is_empty() {
                    return None;
                }
                let mut keys = Vec::new();
                let mut values = Vec::new();
                let mut all_lists = true;
                let mut any_non_empty = false;
                for a in args {
                    let t = self.infer(&a.value);
                    any_non_empty |= matches!(t, Type::NonEmpty(_));
                    match t.peel_non_empty() {
                        Type::List(v) => values.push((**v).clone()),
                        t @ (Type::Array(_) | Type::Shape { .. }) => {
                            all_lists = false;
                            let (k, v) = arrays::iter_key_value(t);
                            keys.push(k);
                            values.push(v);
                        }
                        _ => return None,
                    }
                }
                let v = Type::union(values);
                let merged = if all_lists {
                    Type::List(Box::new(v))
                } else {
                    keys.push(Type::Int); // list parts contribute int keys
                    Type::Array(Some(Box::new((Type::union(keys), v))))
                };
                Some(if any_non_empty {
                    Type::non_empty(merged)
                } else {
                    merged
                })
            }
            // `array_combine($keys, $values)` → `array<value-of-keys, value-of-values>`.
            "array_combine" => {
                let k = self.array_value_type(args.first()?)?;
                let v = self.array_value_type(args.get(1)?)?;
                Some(Type::Array(Some(Box::new((k, v)))))
            }
            // `array_fill($start, $count, $value)` → `array<int, V>`; a
            // positive literal count is non-empty.
            "array_fill" => {
                let v = self.infer(&args.get(2)?.value);
                let filled = Type::Array(Some(Box::new((Type::Int, v))));
                Some(match self.infer(&args.get(1)?.value) {
                    Type::LiteralInt(n) if n >= 1 => Type::non_empty(filled),
                    _ => filled,
                })
            }
            // `array_fill_keys($keys, $value)` → `array<value-of-keys, V>`.
            "array_fill_keys" => {
                let k = self.array_value_type(args.first()?)?;
                let v = self.infer(&args.get(1)?.value);
                Some(Type::Array(Some(Box::new((k, v)))))
            }
            // `array_flip(array<K, V>)` → `array<V, K>`.
            "array_flip" => {
                let t = self.infer(&args.first()?.value);
                let (k, v) = arrays::iter_key_value(&t);
                if matches!(k, Type::Mixed) && matches!(v, Type::Mixed) {
                    return None;
                }
                Some(Type::Array(Some(Box::new((v, k)))))
            }
            // `array_pop`/`array_shift` return an element or `null` when empty.
            "array_pop" | "array_shift" => {
                let v = self.array_value_type(args.first()?)?;
                Some(v.nullable())
            }
            // `array_chunk($a, $n)` → a list of non-empty chunks (re-indexed
            // without the preserve-keys flag).
            "array_chunk" if args.len() == 2 => {
                let v = self.array_value_type(args.first()?)?;
                Some(Type::List(Box::new(Type::non_empty(Type::List(Box::new(
                    v,
                ))))))
            }
            // `range($a, $b)` always yields at least one element.
            "range" => {
                let int_ish =
                    |t: &Type| matches!(t, Type::Int | Type::LiteralInt(_) | Type::IntRange { .. });
                let a = self.infer(&args.first()?.value);
                let b = self.infer(&args.get(1)?.value);
                let elem = if int_ish(&a) && int_ish(&b) && args.len() == 2 {
                    Type::Int
                } else if matches!(a, Type::Float) || matches!(b, Type::Float) {
                    Type::Float
                } else {
                    return None;
                };
                Some(Type::non_empty(Type::List(Box::new(elem))))
            }
            // `iterator_to_array($it)` — element types via the iterable
            // machinery; `preserve_keys: false` re-indexes into a list.
            "iterator_to_array" => {
                let t = self.infer(&args.first()?.value);
                let (k, v) = self
                    .index
                    .iterable_key_value_on_type(&t)
                    .unwrap_or_else(|| arrays::iter_key_value(&t));
                if matches!(k, Type::Mixed) && matches!(v, Type::Mixed) {
                    return None;
                }
                let preserve = match args.get(1).map(|a| self.infer(&a.value)) {
                    Some(Type::False) => false,
                    None | Some(Type::True) => true,
                    _ => return None,
                };
                Some(if preserve {
                    Type::Array(Some(Box::new((k, v))))
                } else {
                    Type::List(Box::new(v))
                })
            }
            "array_keys" => Some(Type::List(Box::new(self.array_key_type(args.first()?)?))),
            // `array_values(array<K,V>)` → `list<V>`.
            "array_values" => Some(Type::List(Box::new(self.array_value_type(args.first()?)?))),
            "array_column" => self.array_column_return(args),
            // These keep the value type AND re-index integer keys (default
            // flags), so a list stays a list; returning the input type holds.
            "array_reverse" | "array_slice" | "array_splice" | "array_pad" => {
                match self.infer(&args.first()?.value) {
                    t @ (Type::Array(_) | Type::List(_)) => Some(t),
                    _ => None,
                }
            }
            // These keep the value type but *preserve keys while dropping
            // entries* — a list comes out with holes, i.e. `array<int, V>`,
            // NOT `list<V>` (phpstan models this; `arrayValues.list` relies
            // on the distinction: `array_values(array_filter($list))` is a
            // meaningful call).
            "array_filter" | "array_unique" | "array_diff" | "array_intersect" => {
                match self.infer(&args.first()?.value) {
                    Type::List(v) => Some(Type::Array(Some(Box::new((Type::Int, *v))))),
                    t @ Type::Array(_) => Some(t),
                    _ => None,
                }
            }
            // `max`/`min`: a single iterable arg yields its value type; otherwise
            // the union of the argument types. The stub's `int|float` otherwise
            // poisons `int`-typed uses (e.g. `str_repeat(' ', max(0, $n - $w))`).
            "max" | "min" => {
                if args.len() == 1 {
                    return self.array_value_type(args.first()?);
                }
                let tys: Vec<Type> = args.iter().map(|a| self.infer(&a.value)).collect();
                Some(Type::union(tys))
            }
            // `abs` preserves int/float.
            "abs" => match self.infer(&args.first()?.value) {
                Type::Int | Type::LiteralInt(_) => Some(Type::Int),
                Type::Float => Some(Type::Float),
                _ => None,
            },
            // `array_search($needle, $haystack)` returns the *key* of the haystack
            // (or `false`). The stub's `int|string|false` poisons int-keyed (list)
            // uses — `array_splice($list, array_search(...), …)` after `!== false`.
            "array_search" => {
                let key = self.array_key_type(args.get(1)?)?;
                Some(Type::union(vec![key, Type::False]))
            }
            // `array_key_first`/`array_key_last` return the key (or `null`).
            "array_key_first" | "array_key_last" => {
                let key = self.array_key_type(args.first()?)?;
                Some(Type::union(vec![key, Type::Null]))
            }
            // `count_chars($s, $mode)`: modes 0-2 return an array, mode 3/4 a string.
            // The stub's `array|string` poisons `strlen(count_chars($s, 3))`.
            "count_chars" => match self.infer(&args.get(1)?.value) {
                Type::LiteralInt(3) | Type::LiteralInt(4) => Some(Type::String),
                Type::LiteralInt(0..=2) => Some(Type::Array(None)),
                _ => None,
            },
            _ => None,
        }
    }

    pub(crate) fn array_map_return(&self, args: &[Arg]) -> Option<Type> {
        if self.native {
            return None;
        }
        let callback = args.first()?;
        let inferred_params: Vec<Type> = args
            .iter()
            .skip(1)
            .map(|a| self.array_value_type(a).unwrap_or(Type::Mixed))
            .collect();
        if inferred_params.is_empty() {
            return None;
        }
        let ret = self.callback_return_type(callback, &inferred_params)?;
        if template_observation_is_imprecise(&ret) {
            return None;
        }
        // With multiple arrays PHP re-indexes sequentially (a list); with one
        // array the input's KEYS are preserved, so the result is a list only
        // when the input is one. `array_map($cb, array_filter($list))` keeps
        // the filter's holes — claiming `list` here would false-flag the
        // `array_values()` call that re-indexes it.
        if args.len() > 2 {
            return Some(Type::List(Box::new(ret)));
        }
        match self.infer(&args.get(1)?.value) {
            Type::List(_) => Some(Type::List(Box::new(ret))),
            input @ (Type::Array(_) | Type::Shape { .. } | Type::Iterable(_)) => {
                let key = arrays::array_key_type(&input)
                    .unwrap_or_else(|| Type::union(vec![Type::Int, Type::String]));
                Some(Type::Array(Some(Box::new((key, ret)))))
            }
            _ => None,
        }
    }

    /// Return refinements for the string builtins (phpstan's per-function
    /// DynamicReturnTypeExtensions, batch B1): literal folding where the value
    /// is fully known, non-emptiness where the output provably has a byte.
    /// `None` falls back to the stub signature.
    pub(crate) fn string_builtin_return(&self, fname: &str, args: &[php_ast::Arg]) -> Option<Type> {
        let lit = |i: usize| -> Option<String> {
            match self.infer(&args.get(i)?.value) {
                Type::LiteralString(s) => Some(s.to_string()),
                _ => None,
            }
        };
        let arg_non_empty = |i: usize| -> bool {
            match args.get(i).map(|a| self.infer(&a.value)) {
                Some(Type::LiteralString(s)) => !s.is_empty(),
                Some(Type::StringOf(r)) => r.implies(php_types::StringRefinement::NonEmpty),
                _ => false,
            }
        };
        let non_empty_string = || Type::StringOf(php_types::StringRefinement::NonEmpty);
        Some(match fname {
            // A `%`-free literal format is the result verbatim; with
            // conversions, every specifier but `%s` emits at least one char, so
            // stripping `%%` and `%s` from a literal format proves
            // non-emptiness when anything remains (positional `%1$s` forms are
            // skipped via the `$` guard).
            "sprintf" | "vsprintf" => {
                let fmt = lit(0)?;
                if !fmt.contains('%') {
                    if fmt.is_empty() {
                        return None;
                    }
                    return Some(Type::LiteralString(fmt.into()));
                }
                if fmt.contains('$') {
                    return None;
                }
                let stripped = fmt.replace("%%", "").replace("%s", "");
                if stripped.is_empty() {
                    return None;
                }
                non_empty_string()
            }
            // `explode` with a non-empty separator and no limit always yields
            // at least one element (the whole string when the separator is
            // absent). A `limit` argument can produce an empty list.
            "explode" => {
                let base = Type::List(Box::new(Type::String));
                if args.len() == 2 && arg_non_empty(0) {
                    Type::non_empty(base)
                } else {
                    base
                }
            }
            // Length-preserving transforms: fold literals (byte-wise ASCII
            // semantics since PHP 8.0), keep non-emptiness otherwise.
            "strtolower" | "strtoupper" | "ucfirst" | "lcfirst" | "strrev" => {
                match self.infer(&args.first()?.value) {
                    Type::LiteralString(s) => {
                        let s = s.to_string();
                        Type::LiteralString(
                            match fname {
                                "strtolower" => s.to_ascii_lowercase(),
                                "strtoupper" => s.to_ascii_uppercase(),
                                "ucfirst" => ascii_change_first(&s, true),
                                "lcfirst" => ascii_change_first(&s, false),
                                _ => s.chars().rev().collect(),
                            }
                            .into(),
                        )
                    }
                    Type::StringOf(r) if r.implies(php_types::StringRefinement::NonEmpty) => {
                        non_empty_string()
                    }
                    _ => return None,
                }
            }
            // Default-charlist trim of a literal folds exactly.
            "trim" | "ltrim" | "rtrim" if args.len() == 1 => {
                let s = lit(0)?;
                const WS: &[char] = &[' ', '\t', '\n', '\r', '\0', '\x0B'];
                let folded = match fname {
                    "trim" => s.trim_matches(WS),
                    "ltrim" => s.trim_start_matches(WS),
                    _ => s.trim_end_matches(WS),
                };
                Type::LiteralString(folded.into())
            }
            // `str_repeat`: two known literals fold (size-capped); a non-empty
            // subject repeated a provably-positive count stays non-empty.
            "str_repeat" => {
                let times = match self.infer(&args.get(1)?.value) {
                    Type::LiteralInt(n) => Some(n),
                    Type::IntRange { min: Some(m), .. } if m >= 1 => None,
                    _ => return None,
                };
                match (lit(0), times) {
                    (Some(s), Some(n))
                        if n >= 0 && s.len().saturating_mul(n as usize) <= FOLD_CAP =>
                    {
                        Type::LiteralString(s.repeat(n as usize).into())
                    }
                    _ if arg_non_empty(0) => non_empty_string(),
                    _ => return None,
                }
            }
            // `str_pad($s, $len)`: the result has max(len, strlen) bytes.
            "str_pad" => {
                let len_positive = matches!(
                    self.infer(&args.get(1)?.value),
                    Type::LiteralInt(n) if n >= 1
                );
                if len_positive || arg_non_empty(0) {
                    non_empty_string()
                } else {
                    return None;
                }
            }
            // `number_format` always prints at least one digit.
            "number_format" => non_empty_string(),
            // `date` with a non-empty literal format emits at least one char
            // (every format char produces output; literal chars pass through).
            "date" | "gmdate" => {
                if lit(0)?.is_empty() {
                    return None;
                }
                non_empty_string()
            }
            // `dirname('')` is `'.'` — always non-empty. `uniqid` likewise.
            "dirname" | "uniqid" => non_empty_string(),
            // `gettype` returns one of a fixed non-empty word set.
            "gettype" => non_empty_string(),
            // `filter_var($v, FILTER_VALIDATE_*)` — the filter constant names
            // the success type (failure is `false`; flag args are skipped).
            "filter_var" if args.len() == 2 => {
                let ExprKind::Name(n) = &args[1].value.kind else {
                    return None;
                };
                let success = match last_segment(&n.text) {
                    "FILTER_VALIDATE_INT" => Type::Int,
                    "FILTER_VALIDATE_FLOAT" => Type::Float,
                    "FILTER_VALIDATE_BOOLEAN" | "FILTER_VALIDATE_BOOL" => {
                        // Failure also yields `false` — plain bool covers it.
                        return Some(Type::Bool);
                    }
                    "FILTER_VALIDATE_EMAIL"
                    | "FILTER_VALIDATE_URL"
                    | "FILTER_VALIDATE_IP"
                    | "FILTER_VALIDATE_DOMAIN"
                    | "FILTER_VALIDATE_MAC" => Type::String,
                    _ => return None,
                };
                Type::union(vec![success, Type::False])
            }
            // `preg_split` without flags yields at least one piece (or `false`
            // on a bad pattern). The 4th (flags) arg can produce an empty list.
            "preg_split" if args.len() <= 3 => Type::union(vec![
                Type::non_empty(Type::List(Box::new(Type::String))),
                Type::False,
            ]),
            // `parse_url($url)` → the component shape (all keys optional) or
            // `false` on a seriously malformed URL.
            "parse_url" if args.len() == 1 => {
                let f = |key: &str, ty: Type| php_types::ShapeField {
                    key: Some(key.to_string()),
                    optional: true,
                    ty,
                };
                Type::union(vec![
                    Type::Shape {
                        fields: vec![
                            f("scheme", Type::String),
                            f("host", Type::String),
                            f("port", Type::Int),
                            f("user", Type::String),
                            f("pass", Type::String),
                            f("path", Type::String),
                            f("query", Type::String),
                            f("fragment", Type::String),
                        ],
                        sealed: true,
                    },
                    Type::False,
                ])
            }
            // `pathinfo($p)` → its documented shape (`basename`/`filename`
            // always present); the 2-arg component form returns a string.
            "pathinfo" => {
                if args.len() >= 2 {
                    return Some(Type::String);
                }
                let f = |key: &str, optional: bool| php_types::ShapeField {
                    key: Some(key.to_string()),
                    optional,
                    ty: Type::String,
                };
                Type::Shape {
                    fields: vec![
                        f("dirname", true),
                        f("basename", false),
                        f("extension", true),
                        f("filename", false),
                    ],
                    sealed: true,
                }
            }
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use php_reflect::ReflectionIndex;

    /// Every name this module special-cases must actually BE a built-in in the
    /// stub manifests. The name strings were previously unchecked, so a typo
    /// (`"array_fitler"`) would silently disable the capability forever.
    #[test]
    fn every_special_cased_name_is_a_real_builtin() {
        let builtins = php_types::builtins::functions_for(php_types::PhpVersion::default());
        let known: std::collections::HashSet<String> = builtins
            .iter()
            .map(|f| f.fqn.trim_start_matches('\\').to_ascii_lowercase())
            .collect();

        let mut checked = 0;
        // `eval` is a language construct, not a function, so it is legitimately
        // absent from the function manifest.
        for name in VARIABLE_ESCAPE_FUNCTIONS.iter().filter(|n| **n != "eval") {
            assert!(known.contains(*name), "escape fn {name:?} is not a builtin");
            checked += 1;
        }
        for name in [
            "array_map",
            "array_filter",
            "array_walk",
            "usort",
            "uasort",
            "uksort",
            "preg_replace_callback",
        ] {
            assert!(
                callback_spec(name).is_some(),
                "{name:?} lost its callback spec"
            );
            assert!(
                known.contains(name),
                "callback fn {name:?} is not a builtin"
            );
            checked += 1;
        }
        // The purity list is 72 previously-unchecked name strings.
        for name in PURE_BUILTINS {
            assert!(
                known.contains(*name),
                "PURE_BUILTINS names {name:?}, which is not a builtin function"
            );
            checked += 1;
        }
        assert!(checked >= 80, "table shrank unexpectedly: {checked}");
    }

    #[test]
    fn callback_specs_point_at_the_callable_argument() {
        // `array_map(callback, ...arrays)` — callback first.
        assert_eq!(callback_spec("array_map").unwrap().callback, 0);
        // Everything else takes the array first.
        for name in ["array_filter", "array_walk", "usort", "uksort"] {
            assert_eq!(callback_spec(name).unwrap().callback, 1, "{name}");
        }
        assert!(callback_spec("str_replace").is_none());
    }

    /// Parse `src`, find the call to `call_text`, and ask the guard about it.
    ///
    /// The `Name` comes from the parser rather than being hand-built, so the
    /// fully-qualified/unqualified distinction is exactly what real code produces.
    fn ctx_resolves_builtin(src: &str, call_text: &str) -> bool {
        let full = format!("<?php {src}");
        let r = php_parser::parse(&full);
        assert!(!r.has_errors(), "parse errors in: {src}");
        let mut index = ReflectionIndex::with_builtins();
        index.add_file(&r.program, &r.interner);
        let mut answer = None;
        php_resolve::for_each_region(&r.program.stmts, &r.interner, |scope, region| {
            let ctx = TypeCtx::new(&index, scope, &r.interner);
            for st in region {
                php_ast::walk::for_each_expr_in_stmt(st, &mut |e| {
                    let ExprKind::Call { callee, .. } = &e.kind else {
                        return;
                    };
                    let ExprKind::Name(n) = &callee.kind else {
                        return;
                    };
                    if n.text.eq_ignore_ascii_case(call_text) {
                        let fq_wanted = call_text.starts_with('\\');
                        if (n.fq == php_ast::NameFq::Fq) == fq_wanted {
                            answer = Some(ctx.resolves_to_builtin(n));
                        }
                    }
                });
            }
        });
        answer.unwrap_or_else(|| panic!("no call to {call_text:?} found in: {src}"))
    }

    /// The shadow matrix: built-in knowledge must not apply through a userland
    /// function of the same name, must apply when nothing shadows it, and must
    /// always apply to a fully-qualified call.
    #[test]
    fn shadowing_guard_matrix() {
        // No shadow: PHP's global-function fallback reaches the builtin.
        assert!(ctx_resolves_builtin(
            "namespace App; function f($x) { is_int($x); }",
            "is_int"
        ));
        assert!(ctx_resolves_builtin(
            "namespace App; function f($a) { array_map($a, $a); }",
            "array_map"
        ));
        // A namespaced userland function of the same name shadows it.
        assert!(!ctx_resolves_builtin(
            "namespace App; function is_int($x) { return true; } function f($x) { is_int($x); }",
            "is_int"
        ));
        assert!(!ctx_resolves_builtin(
            "namespace App; function array_map($c, $a) { return []; } function f($a) { array_map($a, $a); }",
            "array_map"
        ));
        // A fully-qualified call always reaches the builtin, shadow or not.
        assert!(ctx_resolves_builtin(
            "namespace App; function is_int($x) { return true; } function f($x) { \\is_int($x); }",
            "\\is_int"
        ));
        // A global userland override shadows it too.
        assert!(!ctx_resolves_builtin(
            "function is_int($x) { return true; } function f($x) { is_int($x); }",
            "is_int"
        ));
    }
}
