# Test fixtures

## `tokens/` — golden lexer fixtures (Tier A)

Each `NAME.php` has a committed `NAME.tokens` produced by PHP's own `token_get_all`, and
`crates/php-lexer/tests/golden_fixtures.rs` asserts our lexer reproduces it exactly.
**Tests and CI never invoke PHP** — the goldens are committed precisely so that stays true.

Format: one token per line, TAB-separated —
`NAME<TAB>start..end<TAB>escaped-text`, where `NAME` is `PhpToken::getTokenName()` (a `T_*`
name, or the literal character for single-char tokens) and the text escapes `\ \n \r \t`.
The harness filters the trivia PHP emits but we deliberately drop (`T_WHITESPACE`,
`T_COMMENT`), while keeping `T_DOC_COMMENT`.

Some fixtures are **deliberately not valid PHP grammar** (e.g. `varoffset_numbers.php`
contains `"$a[12ef]"`, a parse error). That is fine and intentional: this tier's oracle is
`token_get_all`, which tokenizes without parsing. Do not run `php -l` over them.

## Oracle PHP version

**Pinned: PHP 8.5.8 (Homebrew) + `php-ast` 1.1.3.** PHP is not on the default `PATH` in every
shell; prefix commands with:

```sh
export PATH="/opt/homebrew/bin:$PATH"
```

Regenerate the goldens after a lexer change (or an oracle upgrade):

```sh
cargo run -p xtask -- gen-tokens     # rewrites every tokens/*.tokens
git diff test-fixtures/              # review: an unexpected change is a real signal
```

An oracle upgrade should leave every golden **byte-identical** — verified when moving
8.5.7 → 8.5.8. If a golden changes, find out why before committing it: either the lexer
changed (intended) or the oracle's tokenizer did (worth understanding).

### Why the version matters, and how it fails quietly

Two dev-only differential gates depend on this toolchain, and both degrade *silently*:

| Gate | Expected | Failure mode if the oracle is wrong/missing |
|---|---|---|
| `cargo run -p xtask -- difftokens` | 5320/5321 | An older PHP can't emit 8.5+ tokens (`\|>` → `T_PIPE`), so the match rate drops for reasons unrelated to our lexer |
| `cargo run -p xtask -- astdiff` | 5181/5181 (100.00%) | Without the `php-ast` extension it reports **`0/0`** — it does not fail loudly, it compares nothing |

So before treating either number as a regression: check `php -v` and `php -m | grep ast`.
`astdiff` returning `0/0` means "not measured", never "passing".
