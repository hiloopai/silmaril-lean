#!/usr/bin/env sh
# Rebuild wasm/adder.wasm from src/adder.c and check it is byte-identical to the committed file.
# Toolchain: Ubuntu clang 18.1.3 and wasm-ld (LLD) 18.1.3 (see README).
set -eu
cd "$(dirname "$0")"
mkdir -p target
clang --target=wasm32 -mcpu=generic -O2 -ffreestanding -nostdlib \
  -Wl,--no-entry -Wl,--strip-all \
  -o target/adder.wasm src/adder.c
cmp target/adder.wasm wasm/adder.wasm
sha256sum wasm/adder.wasm
