#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/flags.sh"
# zlib sources are compiled verbatim; Z_SOLO removes the libc dependency.
# zlib's own -W noise is not ours to fix, so it is silenced for these TUs only.
( cd "$HERE" && sha256sum -c --quiet zlib-1.3.1.sha256 )
ZFLAGS=(-DZ_SOLO -I"$HERE/zlib-1.3.1" -Wno-sign-compare -Wno-implicit-fallthrough)

# Variant A (default, O1 and O2): under Z_SOLO, Z_U4/Z_U8 are undefined, so
# crc32.c compiles its byte-at-a-time table loop (W undefined, N=5 unused).
EXTRA_CFLAGS=("${ZFLAGS[@]}")
ladder_rung "$HERE" zlib-checksums "$HERE/zlib-1.3.1/adler32.c" "$HERE/zlib-1.3.1/crc32.c" "$HERE/main.c"

# Variant B (O2 only): supply Z_U4/Z_U8 as a hosted build would, enabling the
# W=8, N=5 braided CRC (crc_braid_table, 64-bit words) -- the realistic and
# much harder TV target.  Output under build/braid/build/O2.
mkdir -p "$HERE/build/braid"
EXTRA_CFLAGS=("${ZFLAGS[@]}" -DZ_U4=unsigned "-DZ_U8=unsigned long")
OPTS=-O2 ladder_rung "$HERE/build/braid" zlib-checksums-braid \
  "$HERE/zlib-1.3.1/adler32.c" "$HERE/zlib-1.3.1/crc32.c" "$HERE/main.c"
