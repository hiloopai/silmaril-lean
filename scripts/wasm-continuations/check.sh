#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")/../.."
lake=${LAKE:-lake}
testdir=scripts/wasm-continuations
target=+Silmaril.Wasm.Binaryen.Continuation.Examples
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

"$lake" build --wfail "$target"
"$lake" env lean -DwarningAsError=true --run "$testdir/Interop.lean" emit "$tmp/exact.wasm"
if [ -n "${BINARYEN_BIN:-}" ]; then
  "$BINARYEN_BIN/wasm-shell" --version | grep -F 'version 133'
  "$BINARYEN_BIN/wasm-shell" "$testdir/order.wast"
  "$BINARYEN_BIN/wasm-opt" --enable-multivalue "$tmp/exact.wasm" -o "$tmp/normalized.wasm"
  "$lake" env lean -DwarningAsError=true --run "$testdir/Interop.lean" normalized "$tmp/normalized.wasm"
else
  echo 'BINARYEN_BIN unset: skipping upstream Binaryen 133 interop'
fi
