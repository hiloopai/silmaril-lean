#!/usr/bin/env bash
# Native measurements over exactly the seven ELF-reader pins; no proof claims.
set -euo pipefail
cd "$(dirname "$0")/../.."
examples/elf/pin.sh --check >&2
exec .lake/build/bin/elf-region-inventory \
  examples/dyn/pinned/hello-gcc \
  examples/dyn/pinned/hello-clang \
  examples/elf/pinned/gnu-sha256sum \
  examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums \
  examples/elf/pinned/zlib-libz.so.1.3 \
  examples/elf/pinned/glibc-libm.so.6 \
  examples/elf/pinned/glibc-libc.so.6
