#!/bin/sh
# Compile par_hash.c natively against the vendored zlib 1.3.1 of rung 03 (-DZ_SOLO) and run it.
# Expected (ParHash.tiny, computed in Lean by #eval of ParHash.leaf/root):
#   res[0] = 1281784366, res[1] = 2883475241, out = 3338006634
set -eu
here=$(cd "$(dirname "$0")" && pwd)
z="$here/../../elf-ladder/03-zlib-checksums/zlib-1.3.1"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
gcc -O2 -DZ_SOLO -I"$z" -o "$out/par_hash" "$here/par_hash.c" "$z/crc32.c" -lpthread
"$out/par_hash"
