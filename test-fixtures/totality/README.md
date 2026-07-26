# Totality fixtures — the committed Tier-C canary

Consumed by `crates/php-parser/tests/totality.rs`, which runs in the default
`cargo test --workspace` profile.

The real Tier C (`xtask corpus`, `xtask astdiff`, `xtask difftokens`) needs the
gitignored `php-src` checkout and a local PHP with the php-ast extension, so CI
cannot run it — which left the parser's **totality** guarantee, the invariant
every later layer rests on, with no automated coverage at all. These fixtures
close that gap cheaply.

## The contract

For **every** file here, valid or not:

- lexing and parsing never panic,
- they terminate (a recovery loop that stops advancing hangs the test — this is
  what the `ensure_progress` guard exists to prevent),
- every expression, statement and diagnostic span stays inside the source.

A fixture named `valid_*.php` additionally must parse with **zero diagnostics**.
Everything else is deliberately malformed; the test asserts nothing about *which*
errors come out, only that we survive producing them.

## What is here, and why

These are adversarial inputs, not a sample of ordinary PHP — normal syntax is
already covered by the golden token fixtures (Tier A) and the AST snapshots
(Tier B). The categories are the ones that actually break a hand-written
recursive-descent parser:

| Group | Guards against |
|---|---|
| `deep_*.php` | stack overflow; the `MAX_DEPTH` recursion guard must fire instead of aborting |
| `unterminated_*.php`, `truncated_*.php` | error recovery that never terminates or loses its progress guard |
| `lone_operators`, `stray_closers`, `empty_file`, `html_only`, `bare_open_tag_only` | degenerate token streams |
| `cr_only_newlines`, `interp_edges`, `nested_interp_braces`, `halt_compiler`, `null_bytes_and_high_bytes` | lexer state-machine edges, including non-UTF-8 bytes |
| `valid_modern_syntax.php` | that the whole modern surface still parses clean (enums, hooks, attributes, DNF types, first-class callables, heredoc, interpolation, destructuring) |

## Adding a fixture

Drop a `.php` file in. Name it `valid_*` **only** if `php -l` accepts it — the
test will demand zero diagnostics. Verify the intent first:

```sh
export PATH="/opt/homebrew/bin:$PATH"
php -l test-fixtures/totality/<name>.php
```

Deprecation notices are fine (`${var}` interpolation raises one on 8.5); a
*parse error* means the file must not be named `valid_*`.

There is no generated companion file, so nothing needs regenerating — unlike
`test-fixtures/tokens/`, these are inputs only.
