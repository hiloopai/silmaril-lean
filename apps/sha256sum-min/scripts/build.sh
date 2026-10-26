#!/usr/bin/env bash
# Pinned build of the sha256sum corpus. Usage: scripts/build.sh SILMARIL_CHECKOUT
# Inputs: src/ (this repo), and xcompile/wrappers/xc_sha256.c +
# tests/x86/sha256_compress_clang_O2.hex from SILMARIL_CHECKOUT's origin/main.
set -euo pipefail
R=$(cd "$(dirname "$0")/.." && pwd)
S=${1:?silmaril checkout}
B=$R/build; C=$R/corpus/bin
mkdir -p "$B" "$C"
cd "$R/src"

# Inputs from silmaril origin/main (recorded in the manifest by commit).
git -C "$S" show origin/main:tests/x86/sha256_compress_clang_O2.hex > "$B/sha256_compress_clang_O2.hex"
git -C "$S" show origin/main:xcompile/wrappers/xc_sha256.c > "$B/xc_sha256.c"
python3 -I "$R/scripts/gen_compress_S.py" "$B/sha256_compress_clang_O2.hex" "$B/compress_clang_O2.S"
cmp "$B/compress_clang_O2.S" "$R/src/compress_clang_O2.S"
# The gcc variant compiles only sha256_compress from xc_sha256.c (the rest
# of that file wraps the amosnier library, which is not linked here).
{ echo '#include <stdint.h>'; sed -n '/^void sha256_compress/,$p' "$B/xc_sha256.c"; } > "$B/xc_sha256_compress.c"

CFLAGS=(-O2 -std=gnu11 -ffreestanding -fno-builtin -fno-stack-protector
  -fcf-protection=none -mgeneral-regs-only -fno-pic -fno-pie
  -fno-asynchronous-unwind-tables -fno-unwind-tables -fno-jump-tables
  -fno-tree-vectorize -fno-tree-slp-vectorize -fno-bit-tests -fno-if-conversion
  -fno-if-conversion2 -ffunction-sections -fdata-sections
  -fno-ident -Wall -Wextra -Wno-unused-parameter)
LDFLAGS=(-nostdlib -static -no-pie -Wl,--gc-sections -Wl,--build-id=none
  -Wl,-z,noexecstack -Wl,-z,norelro -Wl,-e,_start)

gcc "${CFLAGS[@]}" -c sha256sum.c -o "$B/sha256sum.o"
gcc -c start.S -o "$B/start.o"
gcc -c "$B/compress_clang_O2.S" -o "$B/compress_clang_O2.o"
gcc "${CFLAGS[@]}" -c "$B/xc_sha256_compress.c" -o "$B/compress_gcc_O2.o"

gcc "${LDFLAGS[@]}" "$B/start.o" "$B/sha256sum.o" "$B/compress_clang_O2.o" -o "$C/sha256sum-min"
gcc "${LDFLAGS[@]}" "$B/start.o" "$B/sha256sum.o" "$B/compress_gcc_O2.o" -o "$C/sha256sum-min-gcc"
echo built "$C/sha256sum-min" "$C/sha256sum-min-gcc"
