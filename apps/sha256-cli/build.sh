#!/usr/bin/env bash
# Pinned build of the freestanding sha256 filter. gcc 13.3.0 (xcompile/toolchains.toml),
# GNU binutils 2.42. Output: build/sha256 (static ET_EXEC, no libc).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
out="$here/build"
mkdir -p "$out"
want_gcc="13.3.0"
got_gcc="$(gcc -dumpfullversion)"
[ "$got_gcc" = "$want_gcc" ] || { echo "need gcc $want_gcc, have $got_gcc" >&2; exit 1; }
python3 -I "$here/gen_compress_s.py" "$repo/Silmaril/Crypto/X86/Sha256O2/Image.lean" "$out/sha256_compress_clang_o2.S"
cmp "$out/sha256_compress_clang_o2.S" "$here/src/sha256_compress_clang_o2.S"
CFLAGS=(-O2 -std=gnu11 -ffreestanding -fno-builtin -fno-pie -fno-stack-protector
        -fcf-protection=none -mgeneral-regs-only -fno-tree-vectorize
        -fno-tree-loop-distribute-patterns -fno-unroll-loops -fno-asynchronous-unwind-tables
        -fno-unwind-tables -fno-ident -Wall -Wextra -Werror)
LDFLAGS=(-static -nostdlib -no-pie -Wl,--build-id=none -Wl,-z,noseparate-code
         -Wl,-z,norelro -Wl,-z,noexecstack -Wl,--no-dynamic-linker)
cd "$here/src"
gcc "${CFLAGS[@]}" -c sha256.c -o "$out/sha256.o"
gcc -c start.S -o "$out/start.o"
gcc -c sha256_compress_clang_o2.S -o "$out/compress.o"
gcc "${CFLAGS[@]}" "${LDFLAGS[@]}" "$out/start.o" "$out/sha256.o" "$out/compress.o" -o "$out/sha256"
sha256sum "$out/sha256"
