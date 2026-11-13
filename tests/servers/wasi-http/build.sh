#!/usr/bin/env bash
# Build the example wasi:http proxy components of Silmaril.Servers.WasiExamples (and the
# filesystem servers store and static) from their WAT sources: each core module is common.wat
# plus one server's part (for store and static, between fs-imports.wat and fs.wat), given the
# component type of a world of world.wit (over the WIT of specs/wasi/0.2.12: `server`, or
# `fs-server` for the filesystem servers) and turned into a component.
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
for s in hello route echo store static; do
  case $s in
    store | static) world=fs-server parts=("$here/fs-imports.wat" "$here/common.wat" "$here/fs.wat" "$here/$s.wat") ;;
    *) world=server parts=("$here/common.wat" "$here/$s.wat") ;;
  esac
  { echo "(module"; cat "${parts[@]}"; echo ")"; } > "$out/$s.core.wat"
  wasm-tools parse "$out/$s.core.wat" -o "$out/$s.core.wasm"
  wasm-tools component embed "$wit" -w "$world" "$out/$s.core.wasm" -o "$out/$s.embed.wasm"
  wasm-tools component new "$out/$s.embed.wasm" -o "$out/$s.wasm"
  wasm-tools validate "$out/$s.wasm"
  echo "built $out/$s.wasm"
done
