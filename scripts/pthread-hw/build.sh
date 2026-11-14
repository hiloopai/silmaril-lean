#!/usr/bin/env bash
# Build the pthread test programs against the host glibc and print their pins.
#   scripts/pthread-hw/build.sh OUTDIR
# Flags are fixed so that the pins are reproducible with the same gcc and glibc.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=${1:?usage: build.sh OUTDIR}
mkdir -p "$out"
CFLAGS="-O2 -Wall -Werror -pthread -fno-stack-protector -fcf-protection=none"
for src in "$here"/src/*.c; do
  name=$(basename "$src" .c)
  gcc $CFLAGS "$src" -o "$out/$name"
done
{
  echo "# gcc: $(gcc --version | head -1)"
  echo "# glibc: $(ldd --version | head -1)"
  echo "# libc.so.6: $(sha256sum /lib/x86_64-linux-gnu/libc.so.6 | cut -d' ' -f1)"
  echo "# flags: $CFLAGS"
  (cd "$out" && sha256sum p* x*)
} | tee "$out/PINS"
