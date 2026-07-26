# Changelog

All notable changes to phpxray are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- A real installer at `install.sh`, attached to each release: it verifies the
  download's sha256 and installs system-wide to `/usr/local/bin`, escalating via
  `sudo`/`doas` only when needed and only prompting when a terminal is attached.
  Works unprivileged in a Docker build, non-interactively in CI, and on busybox
  (`ash`/`wget`/no `install`). Replaces cargo-dist's shell installer, which could
  only install into `~/.cargo/bin` and edited shell profiles to fix up PATH.

## [0.2.0] - 2026-07-26

### Added

- `laravelAliases` config option: register Laravel facade aliases from `config/app.php`
  and package `installed.json` so facade names resolve instead of reporting
  `class.notFound`.
- Unknown config keys now warn with a did-you-mean suggestion instead of being
  silently ignored.
- Wider `--fix` coverage: inherited-ancestor `@var` for untyped property overrides,
  `@return void` for valueless bodies, stale-doc rewrite and deletion repairs,
  unused-`use` capture removal, and inline-`@var` generic completion.
- Byte-range replace fixes alongside docblock insertion, so a fix can rewrite or
  delete existing source.

### Changed

- Builtin stub manifests regenerated from phpstorm-stubs v2026.2.
- Builtin function knowledge (return specializations, callback table, purity, and the
  userland-shadowing guard) consolidated into a single module.
- Enums now carry their implicit `UnitEnum`/`BackedEnum` interfaces.
- First-class-callable placeholders are their own AST node rather than a dropped detail.

### Fixed

- Two panics in flow analysis: an integer overflow, and a copied-callable clobber.
- Constant folding stayed total when integer division overflows.
- Watch/incremental correctness: the stub, baseline and alias files analysis depends on
  are now watched; inline ignores are honoured only in analyzed files; a file's findings
  are cleared when it becomes scan-only; Laravel aliases register in incremental
  sessions; config sections are length-prefixed in the analysis fingerprint.
- Lexer: var-offset numbers are scanned by radix; an interpolated binary string lexes as
  one opening delimiter.
- Parser: doc comments attach across intervening plain comments and are found by binary
  search; a bare `yield` before a colon and an attribute inside a `clone` call are
  accepted; an attribute in a position PHP rejects is reported.
- Name resolution: fully qualified `true`/`false`/`null`, qualified callables resolved
  through the class import table, and expressions inside computed member names.
- Inference: corrected four builtin return over-claims, two over-narrowing paths in
  interprocedural return refinement, unbound templates treated as possibly null, catch
  bodies merged into the definedness environment, and array shapes modeled through
  auto-vivification and branch merges.
- Rules: class-likes declared inside function bodies are analysed, member-existence
  checks are gated correctly, mixed is reported only where the target constrains the
  position, and extra arguments to methods reading `func_get_args` are no longer flagged.
- GitHub annotation output escapes property separators.

## [0.1.0] - 2026-07-24

Initial public release.

[Unreleased]: https://github.com/benpoulson/phpxray/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/benpoulson/phpxray/releases/tag/v0.2.0
[0.1.0]: https://github.com/benpoulson/phpxray/releases/tag/v0.1.0
