#!/usr/bin/env bash
# Rebuild scaled.o (a relocatable object whose .text carries two relocations) into OUT (default: a
# temporary file) and compare it with the pinned scaled.o. The pinned object was built with
# gcc (Debian 14.2.0-19) 14.2.0; another compiler version may produce other bytes.
set -euo pipefail
cd "$(dirname "$0")"
out=${1:-$(mktemp)}
gcc -O2 -c -fno-asynchronous-unwind-tables -fno-ident -fcf-protection=none scaled.c -o "$out"
want=$(cut -d' ' -f1 scaled.o.sha256)
got=$(sha256sum < "$out" | cut -d' ' -f1)
sha256sum -c scaled.o.sha256
[ "$got" = "$want" ] || { echo "build.sh: $out ($got) differs from the pinned scaled.o ($want)" >&2; exit 1; }
echo "build.sh: $out matches the pinned scaled.o"
