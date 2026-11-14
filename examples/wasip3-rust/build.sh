#!/usr/bin/env bash
# Build the WASI 0.3 example components with the pinned toolchain and compare them with the
# committed binaries in dist/ (dist/SHA256SUMS).
#
#   build.sh            build into $CARGO_TARGET_DIR (default $HOME/.cache/wasip3-rust-target),
#                       then check the results against dist/SHA256SUMS
#   build.sh --update   also copy the results into dist/ and rewrite dist/SHA256SUMS
#
# Release builds of hello, echo and cat (opt-level s, LTO, no debug info) and an unoptimised
# debug build of cat (with DWARF: about 3 MB, the large input of the decode certificates).
# Paths are remapped (--remap-path-prefix) so the debug info does not depend on the checkout.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
if ! ./toolchain.sh check; then
  echo "SKIP: pinned Rust toolchain absent (run examples/wasip3-rust/toolchain.sh install)"
  exit 0
fi
eval "$(./toolchain.sh env)"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/.cache/wasip3-rust-target}
export RUSTFLAGS="--remap-path-prefix=$here=/wasip3-rust --remap-path-prefix=$CARGO_HOME=/cargo --remap-path-prefix=$RUSTUP_HOME=/rustup"
cargo build --locked --release --target wasm32-wasip2
cargo build --locked -p cat --target wasm32-wasip2
out=$CARGO_TARGET_DIR/wasm32-wasip2
declare -A built=(
  [hello.wasm]=$out/release/hello.wasm
  [echo.wasm]=$out/release/echo.wasm
  [cat.wasm]=$out/release/cat.wasm
  [cat-debug.wasm]=$out/debug/cat.wasm
)
if [[ ${1:-} == --update ]]; then
  mkdir -p dist
  for n in hello.wasm echo.wasm cat.wasm cat-debug.wasm; do cp "${built[$n]}" "dist/$n"; done
  (cd dist && sha256sum hello.wasm echo.wasm cat.wasm cat-debug.wasm > SHA256SUMS)
fi
status=0
while read -r sum name; do
  got=$(sha256sum "${built[$name]}" | cut -d' ' -f1)
  if [[ $got == "$sum" ]]; then echo "same: $name"; else echo "DIFFERENT: $name ($got)"; status=1; fi
done < dist/SHA256SUMS
exit $status
