#!/bin/sh
#
# phpxray installer.
#
# Installs a prebuilt phpxray binary system-wide (default /usr/local/bin). Written
# for the three places installs actually happen:
#
#   * an interactive machine  -- escalates with sudo/doas, prompting if it must
#   * a Docker build          -- already root, so no escalation, no prompts, no tty
#   * CI                      -- non-interactive; passwordless sudo is used if it
#                                works, otherwise the failure is explicit
#
# It never edits shell profiles: the target directory is expected to be on PATH
# already, and silently rewriting a user's dotfiles is not this script's business.
#
# Usage:
#   curl -fsSL https://github.com/benpoulson/phpxray/releases/latest/download/install.sh | sh
#   curl -fsSL .../install.sh | sh -s -- --dir ~/.local/bin --version 0.2.0
#
# POSIX sh on purpose (dash/busybox/ash), so it runs in minimal containers.
set -eu

REPO="benpoulson/phpxray"
BIN="phpxray"

INSTALL_DIR="${PHPXRAY_INSTALL_DIR:-/usr/local/bin}"
VERSION="${PHPXRAY_VERSION:-latest}"
NO_SUDO="${PHPXRAY_NO_SUDO:-0}"
SKIP_CHECKSUM="${PHPXRAY_SKIP_CHECKSUM:-0}"
QUIET=0

say() { [ "$QUIET" = 1 ] || printf '%s\n' "$*"; }
warn() { printf 'warning: %s\n' "$*" >&2; }
err() { printf 'error: %s\n' "$*" >&2; exit 1; }

usage() {
  cat <<EOF
phpxray installer

Downloads a prebuilt phpxray binary, verifies its checksum, and installs it.

USAGE:
    install.sh [OPTIONS]

OPTIONS:
    -d, --dir <DIR>       Install directory (default: /usr/local/bin)
    -v, --version <VER>   Version to install, e.g. 0.2.0 (default: latest)
        --no-sudo         Never escalate; fail if the directory is not writable
        --skip-checksum   Skip checksum verification (not recommended)
    -q, --quiet           Only print errors
    -h, --help            Print this help

ENVIRONMENT:
    PHPXRAY_INSTALL_DIR, PHPXRAY_VERSION, PHPXRAY_NO_SUDO,
    PHPXRAY_SKIP_CHECKSUM  Same as the flags above.

EXAMPLES:
    # system-wide, escalating if needed
    curl -fsSL https://github.com/$REPO/releases/latest/download/install.sh | sh

    # user-local, no escalation possible or needed
    curl -fsSL https://github.com/$REPO/releases/latest/download/install.sh \\
      | sh -s -- --dir "\$HOME/.local/bin"

    # pinned version in a Dockerfile or CI job
    curl -fsSL https://github.com/$REPO/releases/latest/download/install.sh \\
      | sh -s -- --version 0.2.0
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    -d | --dir) [ $# -ge 2 ] || err "--dir needs a value"; INSTALL_DIR="$2"; shift 2 ;;
    -v | --version) [ $# -ge 2 ] || err "--version needs a value"; VERSION="$2"; shift 2 ;;
    --no-sudo) NO_SUDO=1; shift ;;
    --skip-checksum) SKIP_CHECKSUM=1; shift ;;
    -q | --quiet) QUIET=1; shift ;;
    -h | --help) usage; exit 0 ;;
    *) err "unrecognized option '$1' (try --help)" ;;
  esac
done

# ---------------------------------------------------------------- platform ----

detect_target() {
  os="$(uname -s)"
  arch="$(uname -m)"
  case "$os" in
    Darwin)
      case "$arch" in
        arm64 | aarch64) echo "aarch64-apple-darwin" ;;
        x86_64) echo "x86_64-apple-darwin" ;;
        *) err "unsupported macOS architecture: $arch" ;;
      esac
      ;;
    Linux)
      # Always musl: the published Linux builds are fully static, so they run on
      # any distro and in scratch/distroless images without a libc dependency.
      case "$arch" in
        aarch64 | arm64) echo "aarch64-unknown-linux-musl" ;;
        x86_64 | amd64) echo "x86_64-unknown-linux-musl" ;;
        *) err "unsupported Linux architecture: $arch" ;;
      esac
      ;;
    *)
      err "unsupported operating system: $os (prebuilt binaries cover macOS and Linux)"
      ;;
  esac
}

# ---------------------------------------------------------------- download ----

if command -v curl >/dev/null 2>&1; then
  DOWNLOADER=curl
elif command -v wget >/dev/null 2>&1; then
  DOWNLOADER=wget
else
  err "neither curl nor wget is available"
fi

fetch() {
  # fetch <url> <dest>
  case "$DOWNLOADER" in
    curl) curl --proto '=https' --tlsv1.2 -fsSL "$1" -o "$2" ;;
    wget) wget --https-only -qO "$2" "$1" ;;
  esac
}

# ---------------------------------------------------------------- checksum ----

sha256_of() {
  # sha256_of <file> -- prints the lowercase hex digest
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | cut -d' ' -f1
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | sed 's/.*= *//'
  else
    return 1
  fi
}

verify_checksum() {
  # verify_checksum <dir> <file>
  #
  # The digests are compared directly rather than via `sha256sum -c`, whose
  # input parsing differs across GNU, BSD and busybox -- and whose GNU build
  # warns about the trailing blank line the release artifacts carry.
  if [ "$SKIP_CHECKSUM" = 1 ]; then
    warn "skipping checksum verification"
    return 0
  fi

  expected="$(sed -n 's/^\([0-9a-fA-F]\{64\}\).*/\1/p' "$1/$2.sha256" | head -n 1)"
  [ -n "$expected" ] || err "no sha256 digest found in $2.sha256"

  actual="$(sha256_of "$1/$2")" || err "no sha256sum, shasum or openssl available to \
verify the download; install one, or re-run with --skip-checksum to bypass"

  expected="$(printf '%s' "$expected" | tr 'A-F' 'a-f')"
  actual="$(printf '%s' "$actual" | tr 'A-F' 'a-f')"
  [ "$expected" = "$actual" ] ||
    err "checksum mismatch for $2 (expected $expected, got $actual)"
  say "checksum ok"
}

# -------------------------------------------------------------- escalation ----

# Decide how to run the commands that write into the install directory. Prints
# the prefix to use ("" for direct, otherwise sudo/doas).
escalation_for() {
  dir="$1"

  # Find the nearest existing ancestor; that is what must be writable, since a
  # missing directory has to be created inside it.
  probe="$dir"
  while [ ! -d "$probe" ]; do
    parent="$(dirname "$probe")"
    [ "$parent" != "$probe" ] || break
    probe="$parent"
  done

  if [ -w "$probe" ]; then
    echo ""
    return 0
  fi

  if [ "$(id -u)" = 0 ]; then
    # Root but not writable: read-only mount or similar. Escalation won't help.
    err "$probe is not writable even as root (read-only filesystem?)"
  fi

  if [ "$NO_SUDO" = 1 ]; then
    err "$probe is not writable and escalation is disabled; \
choose a writable --dir (e.g. \$HOME/.local/bin) or drop --no-sudo"
  fi

  for tool in sudo doas; do
    command -v "$tool" >/dev/null 2>&1 || continue
    # A passwordless (or already-cached) escalation is safe to use anywhere,
    # including CI, where there is no tty to answer a prompt.
    if "$tool" -n true >/dev/null 2>&1; then
      echo "$tool"
      return 0
    fi
    # Otherwise only escalate when someone is actually there to type a password.
    # Note this function's stdout is captured by the caller, so the notice goes
    # to stderr -- otherwise it would be parsed as the escalation command.
    if [ -t 0 ] || [ -r /dev/tty ]; then
      [ "$QUIET" = 1 ] ||
        printf '%s needs elevated permissions; %s may prompt for your password\n' \
          "$probe" "$tool" >&2
      echo "$tool"
      return 0
    fi
  done

  err "$probe is not writable and no usable sudo/doas was found; \
re-run as root, or install somewhere writable with --dir \$HOME/.local/bin"
}

# ------------------------------------------------------------------- install --

TARGET="$(detect_target)"
ARCHIVE="$BIN-$TARGET.tar.xz"

if [ "$VERSION" = latest ]; then
  BASE_URL="https://github.com/$REPO/releases/latest/download"
else
  # Accept both "0.2.0" and "v0.2.0".
  case "$VERSION" in v*) tag="$VERSION" ;; *) tag="v$VERSION" ;; esac
  BASE_URL="https://github.com/$REPO/releases/download/$tag"
fi

# Resolve escalation before downloading, so an unwritable target fails in a
# second rather than after pulling down an archive we cannot install.
SUDO="$(escalation_for "$INSTALL_DIR")"

TMPDIR_="$(mktemp -d 2>/dev/null || mktemp -d -t phpxray)"
cleanup() { rm -rf "$TMPDIR_"; }
trap cleanup EXIT
trap 'cleanup; exit 130' INT
trap 'cleanup; exit 143' TERM

say "downloading $BIN ($VERSION) for $TARGET"
fetch "$BASE_URL/$ARCHIVE" "$TMPDIR_/$ARCHIVE" ||
  err "could not download $BASE_URL/$ARCHIVE (does that version exist?)"

if [ "$SKIP_CHECKSUM" != 1 ]; then
  fetch "$BASE_URL/$ARCHIVE.sha256" "$TMPDIR_/$ARCHIVE.sha256" ||
    err "could not download the checksum for $ARCHIVE"
fi
verify_checksum "$TMPDIR_" "$ARCHIVE"

# GNU, BSD and reasonably recent busybox tar all auto-detect xz from -xf; fall
# back to piping through xz for the builds that do not.
if ! tar -xf "$TMPDIR_/$ARCHIVE" -C "$TMPDIR_" 2>/dev/null; then
  if command -v xz >/dev/null 2>&1; then
    xz -dc "$TMPDIR_/$ARCHIVE" | (cd "$TMPDIR_" && tar -xf -) ||
      err "could not extract $ARCHIVE"
  else
    err "could not extract $ARCHIVE: this tar cannot read xz and no xz binary was found"
  fi
fi

SRC="$TMPDIR_/$BIN-$TARGET/$BIN"
[ -f "$SRC" ] || err "the archive did not contain $BIN where expected ($BIN-$TARGET/$BIN)"
chmod +x "$SRC"

[ -d "$INSTALL_DIR" ] || $SUDO mkdir -p "$INSTALL_DIR" ||
  err "could not create $INSTALL_DIR"

# `install` gives us mode-setting and an atomic-enough replace in one step, and
# unlike `cp` it will not fail on a running binary. Fall back for busybox builds
# that ship without it.
if command -v install >/dev/null 2>&1; then
  $SUDO install -m 755 "$SRC" "$INSTALL_DIR/$BIN" || err "could not install to $INSTALL_DIR"
else
  $SUDO cp "$SRC" "$INSTALL_DIR/$BIN.tmp$$" && $SUDO chmod 755 "$INSTALL_DIR/$BIN.tmp$$" &&
    $SUDO mv "$INSTALL_DIR/$BIN.tmp$$" "$INSTALL_DIR/$BIN" ||
    err "could not install to $INSTALL_DIR"
fi

# --------------------------------------------------------------- verify -------

installed_version="$("$INSTALL_DIR/$BIN" --version 2>/dev/null || echo "unknown")"
say "installed $installed_version to $INSTALL_DIR/$BIN"

case ":$PATH:" in
  *":$INSTALL_DIR:"*) ;;
  *) warn "$INSTALL_DIR is not on your PATH; add it or invoke $INSTALL_DIR/$BIN directly" ;;
esac
