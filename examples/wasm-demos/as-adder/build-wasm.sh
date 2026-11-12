#!/usr/bin/env sh
# Rebuild wasm/adder.wasm from assembly/index.ts with the pinned AssemblyScript compiler and
# check it is byte-identical to the committed file.
set -eu
cd "$(dirname "$0")"
out="$(mktemp -d)"
npx --yes -p assemblyscript@0.28.20 asc assembly/index.ts --runtime stub -O3 \
  --outFile "$out/adder.wasm" --textFile "$out/adder.wat"
cmp "$out/adder.wasm" wasm/adder.wasm
cmp "$out/adder.wat" wasm/adder.wat
rm -rf "$out"
sha256sum wasm/adder.wasm
