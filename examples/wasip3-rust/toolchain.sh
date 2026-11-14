#!/usr/bin/env bash
# Install (or locate) the pinned Rust toolchain for the WASI 0.3 examples, under
# ~/.cache/silmaril-tools only (never system-wide):
#
#   toolchain.sh install   download rustup-init 1.29.2 (SHA-256 checked), install Rust 1.99.1
#                          with the wasm32-wasip2 target into ~/.cache/silmaril-tools/rust-1.99.1
#   toolchain.sh env       print the environment lines (eval "$(toolchain.sh env)")
#   toolchain.sh check     exit 0 when the toolchain is installed, 1 otherwise
set -euo pipefail

TOOLS=${SIL_TOOLS:-$HOME/.cache/silmaril-tools}
RUSTUP_VERSION=1.29.2
RUSTUP_SHA256=5be191e8c70a5007074254cb74d78dbfdd25cd5a61c27de7b8e5410122ec24f4
RUST_VERSION=1.99.1
ROOT=$TOOLS/rust-$RUST_VERSION

env_lines() {
  echo "export RUSTUP_HOME=$ROOT/rustup CARGO_HOME=$ROOT/cargo"
  echo "export PATH=$ROOT/cargo/bin:\$PATH"
}

case ${1:-} in
  env) env_lines ;;
  check)
    [[ -x $ROOT/cargo/bin/cargo && -d $ROOT/rustup/toolchains/$RUST_VERSION-x86_64-unknown-linux-gnu/lib/rustlib/wasm32-wasip2 ]]
    ;;
  install)
    dl=$TOOLS/rustup-init-$RUSTUP_VERSION/dl
    if [[ ! -x $dl/rustup-init ]]; then
      mkdir -p "$dl"
      [[ -z $(ls -A "$dl") ]] || { echo "toolchain.sh: $dl is not empty" >&2; exit 1; }
      curl -sSfL -o "$dl/rustup-init" \
        "https://static.rust-lang.org/rustup/archive/$RUSTUP_VERSION/x86_64-unknown-linux-gnu/rustup-init"
    fi
    echo "$RUSTUP_SHA256  $dl/rustup-init" | sha256sum -c -
    chmod +x "$dl/rustup-init"
    mkdir -p "$ROOT"
    RUSTUP_HOME=$ROOT/rustup CARGO_HOME=$ROOT/cargo "$dl/rustup-init" -y --no-modify-path \
      --profile minimal --default-toolchain "$RUST_VERSION" --target wasm32-wasip2
    ;;
  *) sed -n '2,9p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2 ;;
esac
