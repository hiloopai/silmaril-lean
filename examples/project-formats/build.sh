#!/bin/sh
# Rebuild example.o and example-exec.elf bit for bit and check them against RECEIPTS.sha256.
# The registry (silmaril/artifacts.toml) records this as two derivations with status
# `reproduced`. Toolchain: gcc 13.3.0 (Ubuntu 13.3.0-6ubuntu2~24.04.1), GNU ld 2.42, x86_64.
# Usage: build.sh [OUTDIR] (default: a fresh temporary directory).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-$(mktemp -d)}
mkdir -p "$out"
cp "$here/example.c" "$here/example-exec.c" "$out/"
cd "$out"   # compile by relative name: the object's file symbol is `example.c`
gcc -O1 -c -fno-asynchronous-unwind-tables -fno-ident -fno-pic -o example.o example.c
gcc -O1 -static -nostdlib -fno-pic -no-pie -fno-asynchronous-unwind-tables -fno-ident \
  -Wl,--build-id=none -Wl,-z,max-page-size=4096 -Wl,-z,noseparate-code -Wl,-z,norelro \
  -s -o example-exec.elf example-exec.c
sha256sum -c "$here/RECEIPTS.sha256"
echo "built in $out"
