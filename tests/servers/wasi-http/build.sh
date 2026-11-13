#!/usr/bin/env bash
# Build the example wasi:http proxy components of Silmaril.Servers.WasiExamples from their WAT
# sources: each core module is common.wat plus one server's part, given the component type of
# world.wit (over the WIT of specs/wasi/0.2.12) and turned into a component.
#
# Usage: tests/servers/wasi-http/build.sh [OUT_DIR]   (default: build/wasi-http)
# Needs wasm-tools (`nix develop .#http-test` provides the pinned one).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=${1:-$root/build/wasi-http}
mkdir -p "$out"
wit=$(mktemp -d)
trap 'rm -rf "$wit"' EXIT
mkdir -p "$wit/deps"
cp "$here/world.wit" "$wit/"
for p in http io clocks random cli filesystem sockets; do
  cp -r "$root/specs/wasi/0.2.12/$p" "$wit/deps/"
done
for s in hello route echo greet; do
  { echo "(module"; cat "$here/common.wat" "$here/$s.wat"; echo ")"; } > "$out/$s.core.wat"
  wasm-tools parse "$out/$s.core.wat" -o "$out/$s.core.wasm"
  wasm-tools component embed "$wit" -w server "$out/$s.core.wasm" -o "$out/$s.embed.wasm"
  wasm-tools component new "$out/$s.embed.wasm" -o "$out/$s.wasm"
  wasm-tools validate "$out/$s.wasm"
  echo "built $out/$s.wasm"
done
