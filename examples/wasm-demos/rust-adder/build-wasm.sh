#!/usr/bin/env sh
# Rebuild wasm/adder.wasm from source and check it is byte-identical to the committed file.
set -eu
cd "$(dirname "$0")"
rm -rf target/wasm32-unknown-unknown/wasm
cargo build -p adder --profile wasm --target wasm32-unknown-unknown
cmp target/wasm32-unknown-unknown/wasm/adder.wasm wasm/adder.wasm
sha256sum wasm/adder.wasm
