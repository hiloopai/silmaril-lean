#!/bin/sh
# Re-encode the published wasi:io@0.2.12 (OCI) with wasm-wit's verified `encode`
# (Wit.Tool.reencode, reencode_sound) and compare with the tests/wat fixture, which
# wasm-tools 1.263.0 wrote from the wasip2 1.0.4 crate's io.wit.
#   examples/wasm-components/gen/reencode.sh [SIL_WIT]    (from the repository root)
set -eu
W=${1:-.lake/build/bin/wasm-wit}
out=$(mktemp -d)
"$W" encode examples/wasm-components/components/wasi/io-0.2.12.wasm -o "$out/io.wasm"
cmp "$out/io.wasm" tests/wat/fixtures/wasi-io-0.2.12.wasm
sha256sum "$out/io.wasm" | sed "s|$out/io.wasm|tests/wat/fixtures/wasi-io-0.2.12.wasm|"
rm -r "$out"
