#!/usr/bin/env bash
# Rebuild the two objects of the worked example from max2.c with a pinned gcc image.
#   examples/sysv-tv/max2/build.sh && sha256sum -c examples/sysv-tv/max2/RECEIPTS.sha256
set -euo pipefail
cd "$(dirname "$0")"
image=gcc@sha256:b99b86a28812b1e6453a231a947dc43d76fe192788a12f344a9b568bf9f5d24c  # gcc:14.2.0
flags="-c -std=c11 -ffreestanding -fno-builtin -fno-stack-protector -fcf-protection=none
  -mgeneral-regs-only -fno-pic -fno-pie -fno-asynchronous-unwind-tables -fno-unwind-tables
  -fno-ident"
for o in O0 O2; do
  docker run --rm --network host -v "$PWD:/src" -w /src "$image" gcc -$o $flags max2.c -o $o/max2.o
done
