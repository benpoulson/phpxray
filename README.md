# phpxray

A fast PHP static analyzer written in Rust.

`phpxray` parses PHP into a typed AST, resolves names and project symbols, reflects native and PHPDoc
types, runs flow-sensitive inference, and reports PHPStan-style diagnostics through the `phpxray` CLI.
It runs a real project today: parallel parsing and analysis, YAML config, levels `0`–`max`, multiple
reporters, suppression, baselines, dependency-aware incremental watch mode, and **300 rules**.

Two things set it apart from a plain PHPStan clone:

- **It infers signatures for fully untyped code.** Legacy functions/methods where everything is
  `mixed` get parameter and return types reconstructed from their bodies and call sites, so the rest of
  the analysis actually has something to check — something PHPStan structurally can't do.
- **It repairs its own findings.** `phpxray --fix` writes inferred `@var`/`@param`/`@return` PHPDoc back
  into your source for the `missingType.*` family and iterates to convergence.

The analyzer is intentionally conservative: unknown, dynamic, vendor-incomplete, and unresolved cases
fall back to broad types rather than producing noisy false positives.

## Status

- **Parser:** complete for the supported frontend, with 100% structural AST differential coverage
  against Zend's own AST on accepted corpus fixtures.
- **Rules:** 300 registered across levels `0`–`max`, using PHPStan-faithful identifiers (`return.type`,
  `method.notFound`, `argument.type`, …).
- **Type system:** unions/intersections, generics with template bounds, PHPDoc types, reflected
  builtins, flow-sensitive narrowing, callback/closure inference, receiver generics, collection
  callbacks, iterable/generator precision, conditional return types, and strictness gates for higher
  levels.
- **Product:** parallel per-file analysis, whole-project result cache, incremental watch mode, `--fix`,
  untyped-signature inference, config-driven stubs and type aliases.

## Install

### Prebuilt binaries (recommended)

Prebuilt, **fully static** binaries for macOS and Linux (x86-64 and ARM64) are published on the
[Releases](https://github.com/benpoulson/phpxray/releases) page. The Linux builds are static musl —
one file, no shared-library dependencies, runs on any distro (Ubuntu, Alpine, RHEL, …) and in minimal
containers.

```sh
# macOS + Linux — installs into ~/.cargo/bin
curl --proto '=https' --tlsv1.2 -LsSf \
  https://github.com/benpoulson/phpxray/releases/latest/download/phpxray-installer.sh | sh
```

Or via Homebrew (macOS + Linux):

```sh
brew install benpoulson/tap/phpxray
```

### From source

The workspace builds on stable Rust (no nightly features):

```sh
# straight onto your PATH
cargo install --git https://github.com/benpoulson/phpxray phpxray

# or clone and build
git clone https://github.com/benpoulson/phpxray.git
cd phpxray
cargo build -p phpxray --release   # -> target/release/phpxray
```

## Quick Start

```sh
# analyze explicit paths at a chosen level
phpxray -l 6 src tests

# or use an autodiscovered config file (phpxray.yaml / .yml / .dist.yaml)
phpxray

# machine-readable output
phpxray --error-format json

# repair missing PHPDoc types in place
phpxray --fix

# re-analyze incrementally as files change
phpxray --watch

# write a baseline for an existing codebase, then reference it from config
phpxray --generate-baseline
```

## Configuration

Example `phpxray.yaml`:

```yaml
level: 8
paths:
  - src
  - tests

scanPaths:
  - vendor

exclude:
  - generated/**

phpVersion: "8.4"
treatPhpDocTypesAsCertain: true
inferUntypedSignatures: true

baseline: phpxray-baseline.yaml

ignore:
  - identifier: method.notFound
    path: tests/fixtures/**
  - message: '#^Call to an undefined function legacy_#'
```

Common options:

- `level`: `0` through `9`, or `max`.
- `paths`: files or directories to analyze.
- `scanPaths` / `scanFiles`: parse and reflect symbols without reporting diagnostics from them.
- `exclude`: exclude paths from analysis (globs).
- `excludePaths.analyse`: demote paths to scan-only; `excludePaths.analyseAndScan`: exclude entirely.
- `extensions`: file extensions to analyze (default `["php"]`).
- `phpVersion`: target PHP version, used for version-aware builtin signatures.
- `treatPhpDocTypesAsCertain`: matches PHPStan's option of the same name.
- `inferUntypedSignatures`: reconstruct types for untyped functions/methods (default `true`).
- `ignore`: suppress findings by message regex, identifier, path, paths, and/or count.

Additional PHPStan-compatible options:

- `stubFiles`: user-supplied `.stub`/`.php` files whose declarations override or fill in reflection for
  named symbols (third-party signature fixes).
- `typeAliases`: project-wide PHPDoc type aliases (`{ UserId: 'int' }`).
- `earlyTerminatingFunctionCalls` / `earlyTerminatingMethodCalls`: calls that never return (`dd`,
  `abort`, …), so branches calling them are treated like `throw`.
- `checkExplicitMixed`, `checkImplicitMixed`, `checkUninitializedProperties`,
  `checkTooWideReturnTypesInProtectedAndPublicMethods`: per-rule strictness toggles.
- `resultCachePath`, `editorUrl`: cache location and clickable editor links in table output.

An existing `phpstan-baseline.neon` is read directly, so a migrating project's baseline loads unchanged.

## Fixing findings

`phpxray --fix` inserts inferred `@var`/`@param`/`@return` PHPDoc for the `missingType.*` family,
iterating to convergence (each round's added types sharpen inference for the next), then re-reports what
remains. Baselined and ignored findings are never fixed. It is mutually exclusive with `--watch` and
`--generate-baseline`.

## Watch mode

`phpxray --watch` keeps a live session and re-analyzes only the files a change can affect (via a
dependency graph over cross-file lookups), so a single-file edit re-checks just that file and its
dependents. `--watch-delay MS` tunes the debounce.

## Suppressions

Inline suppressions use PHPStan-compatible comments (`@phpxray-ignore` is also accepted):

```php
<?php

// @phpstan-ignore-next-line method.notFound
$user->missingMethod();

$user->missingMethod(); // @phpstan-ignore-line method.notFound
```

## Reporters

Select with `--error-format`:

`table` (default), `json`, `prettyJson`, `raw`, `github`, `checkstyle`, `gitlab`, `junit`.

Exit codes:

- `0`: no errors
- `1`: findings were reported
- `2`: usage or configuration error

## Development

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo run -p xtask -- rule-manifest   # the source of truth for rule coverage
```

CI runs clippy + the test suite on every push and PR to `main`. Useful `xtask` commands include
`corpus`, `astdiff`, `resolve`, `index`, `reflect`, `infer`, `check`, and `rule-timings`. Some
oracle/differential tasks require a local PHP binary and the PHP AST extension; the ordinary Rust test
suite does not require PHP.

## Architecture

The workspace is split into small crates:

- `php-lexer`, `php-parser`, `php-ast`: frontend.
- `php-resolve`, `php-index`: names and project symbols.
- `php-phpdoc`, `php-types`, `php-reflect`: PHPDoc parsing, semantic types, reflection.
- `php-infer`: expression inference, flow, narrowing, assignability, signature inference.
- `php-rules`: diagnostics and rule scheduling.
- `php-config`, `phpxray`: configuration, suppression, baselines, reporters, incremental engine, CLI.
- `xtask`: development and corpus tooling.

Builtins are generated from JetBrains PHPStorm stubs and compiled into version-aware manifests, so the
binary is fully self-contained (no PHP or data files needed at runtime).

## License

MIT.
