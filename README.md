# phpxray

A fast PHP static analyzer written in Rust.

`phpxray` parses PHP into a typed AST, resolves names and project symbols, reflects native and PHPDoc
types, runs flow-sensitive inference, and reports phpstan-style diagnostics through the
`php-analyzer` CLI.

The project is young, but it is not a toy prototype: the parser is differential-tested against Zend's
AST, the CLI can analyze real projects, and the rule engine already covers a broad set of PHPStan-like
checks across levels `0` through `max`.

## Status

- PHP parser: complete for the supported frontend, with 100% structural AST differential coverage on
  accepted Zend corpus fixtures.
- Analyzer CLI: config discovery, rule levels, table/json/github/checkstyle reporters, inline
  suppressions, baselines, scan-only files, parallel per-file analysis, and conservative result caching.
- Type system: unions/intersections, generics, PHPDoc types, reflected builtins, flow-sensitive
  narrowing, callback inference, receiver generics, collection callbacks, iterable/generator precision,
  and strictness gates for higher levels.
- Current focus: improving recall in hard real-world PHP patterns, especially framework collection APIs,
  exception-aware flow, and carefully bounded dynamic PHP behavior.

The analyzer is intentionally conservative. Unknown, dynamic, vendor-incomplete, and unresolved cases
usually fall back to broad types rather than producing noisy false positives.

## Install

Rust nightly is currently used for development.

```sh
git clone https://github.com/benpoulson/phpxray.git
cd phpxray
cargo build -p php-cli --release
```

The binary is built at:

```sh
target/release/php-analyzer
```

For local development, `cargo build -p php-cli` builds `target/debug/php-analyzer`.

## Quick Start

Analyze explicit paths:

```sh
php-analyzer -l 6 src tests
```

Use an autodiscovered config file:

```sh
php-analyzer
```

Supported config names are:

- `phpanalyzer.yaml`
- `phpanalyzer.yml`
- `phpanalyzer.dist.yaml`

JSON output:

```sh
php-analyzer --error-format json
```

Generate a baseline for an existing codebase:

```sh
php-analyzer --generate-baseline
```

Then reference the generated baseline from config.

## Configuration

Example `phpanalyzer.yaml`:

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
reportUnmatchedIgnored: true

baseline: phpanalyzer-baseline.yaml

ignore:
  - identifier: method.notFound
    path: tests/fixtures/**
  - message: '#^Call to an undefined function legacy_#'
```

Important options:

- `level`: `0` through `9`, or `max`.
- `paths`: files or directories to analyze.
- `scanPaths` / `scanFiles`: parse and reflect symbols without reporting diagnostics from those files.
- `exclude`: exclude paths from analysis.
- `excludePaths.analyse`: demote paths to scan-only.
- `excludePaths.analyseAndScan`: exclude paths entirely.
- `extensions`: file extensions to analyze, defaulting to `["php"]`.
- `phpVersion`: target PHP version, used for version-aware builtin signatures.
- `treatPhpDocTypesAsCertain`: matches PHPStan's option of the same name.
- `ignore`: suppress findings by message regex, identifier, path, paths, and/or count.

## Suppressions

Inline suppressions use PHPStan-compatible comments:

```php
<?php

// @phpstan-ignore-next-line method.notFound
$user->missingMethod();

$user->missingMethod(); // @phpstan-ignore-line method.notFound
```

`@php-analyzer-ignore` is also accepted as an alias.

## Reporters

Use `--error-format` with:

- `table`
- `json`
- `github`
- `checkstyle`

Exit codes:

- `0`: no errors
- `1`: findings were reported
- `2`: usage or configuration error

## Development

Common checks:

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo run -p xtask -- infer
```

Useful `xtask` commands:

```sh
cargo run -p xtask -- corpus
cargo run -p xtask -- astdiff
cargo run -p xtask -- resolve
cargo run -p xtask -- index
cargo run -p xtask -- reflect
cargo run -p xtask -- infer
cargo run -p xtask -- rule-manifest
cargo run -p xtask -- rule-timings --path src
```

Some oracle/differential tasks require a local PHP binary and the PHP AST extension. The ordinary Rust
test suite does not require PHP.

## Architecture

The workspace is split into small crates:

- `php-lexer`, `php-parser`, `php-ast`: frontend.
- `php-resolve`, `php-index`: names and project symbols.
- `php-phpdoc`, `php-types`, `php-reflect`: PHPDoc parsing, semantic types, reflection.
- `php-infer`: expression inference, flow, narrowing, assignability.
- `php-rules`: diagnostics and rule scheduling.
- `php-config`, `php-cli`: configuration, suppression, baselines, reporters, and the CLI.
- `xtask`: development and corpus tooling.

Builtins are generated from JetBrains PHPStorm stubs and compiled into version-aware manifests.

## License

MIT.
