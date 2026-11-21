#!/usr/bin/env bash
# Regenerate the per-part ELF reader modules (Silmaril/Elf/Staged/Pinned/*/{Bytes,Defs,Thms}.lean)
# from the pinned files of examples/elf/README.md.
#   scripts/elf-reader/gen.sh [--check]   with --check, fail if a module differs
set -euo pipefail
cd "$(dirname "$0")/../.."
check=${1:-}
examples/elf/pin.sh --check
lake build elf-staged >/dev/null
out=Silmaril/Elf/Staged/Pinned
dir=$out
if [ "$check" = --check ]; then dir=$(mktemp -d); trap 'rm -rf "$dir"' EXIT; fi
sha() { sha256sum "$1" | cut -d' ' -f1; }
# The unverified disassembly listing the explorer shows (examples/elf/disasm/SLUG.objdump): GNU
# objdump's output, with the objdump version on the first line. --check compares it only when the
# local objdump is the recorded version.
listing() {  # listing FILE SLUG
  local f=examples/elf/disasm/$2.objdump v
  # Files over 512 KiB (the glibc libraries): no committed listing; elf-pages disassembles them when
  # it writes the pages (tools/elf-pages, `objdump` on PATH).
  if [ "$(stat -c %s "$1")" -gt 524288 ]; then return; fi
  if ! command -v objdump >/dev/null; then echo "gen.sh: no objdump; $f not regenerated or compared" >&2; return; fi
  v="# $(objdump --version | head -1)"
  if [ "$check" = --check ]; then
    if [ "$(head -1 "$f")" = "$v" ]; then
      cmp -s <(echo "$v"; echo "# objdump -d -w -z $1"; objdump -d -w -z "$1") "$f" || { echo "gen.sh: $f differs" >&2; exit 1; }
    else echo "gen.sh: $f was written by another objdump ($(head -1 "$f")); not compared" >&2; fi
  else
    mkdir -p examples/elf/disasm
    { echo "$v"; echo "# objdump -d -w -z $1"; objdump -d -w -z "$1"; } > "$f"
  fi
}
emit() {  # emit FILE NAME TITLE SLUG
  .lake/build/bin/elf-staged emit-reader "$1" "$2" "$(sha "$1")" "$3" "$dir" >/dev/null
  if [ "$check" = --check ]; then
    for m in Bytes Defs Thms Functions Decomp; do
      cmp -s "$dir/$2/$m.lean" "$out/$2/$m.lean" || { echo "gen.sh: $out/$2/$m.lean differs" >&2; exit 1; }
    done
  fi
  listing "$1" "$4"
}
emit examples/dyn/pinned/hello-gcc HelloGcc '`hello` (gcc 13.3 -O2, dynamically linked against glibc 2.39: `PT_INTERP` ld-linux-x86-64.so.2, `DT_NEEDED` libc.so.6)' hello-gcc
emit examples/dyn/pinned/hello-clang HelloClang '`hello` (clang 18.1 -O2, dynamically linked against glibc 2.39: `PT_INTERP` ld-linux-x86-64.so.2, `DT_NEEDED` libc.so.6)' hello-clang
emit examples/elf/pinned/gnu-sha256sum Sha256sum 'GNU coreutils 9.4 (Ubuntu 9.4-3ubuntu6.3) `sha256sum`' gnu-sha256sum
emit examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums ZlibChecksums 'zlib 1.3.1 `adler32.c` and `crc32.c` (`-DZ_SOLO -O2`, GCC 13.3; `examples/elf-ladder/03-zlib-checksums`)' zlib-checksums
emit examples/elf/pinned/zlib-libz.so.1.3 ZlibLibz 'zlib 1.3 `libz.so.1.3` (Ubuntu zlib1g 1:1.3.dfsg-3.1ubuntu2.3)' zlib-libz
emit examples/elf/pinned/zlib-libz.so.1.2.11 ZlibLibz1211 'zlib 1.2.11 `libz.so.1.2.11` (Ubuntu zlib1g 1:1.2.11.dfsg-2ubuntu9.2)' zlib-libz-1.2.11
emit examples/libs/zlib/pinned/libz.so.1.3.1-gcc-13 ZlibLibz131Gcc 'zlib 1.3.1 `libz.so.1.3.1` (GCC 13.3 `-O2`, upstream tarball; `examples/libs/zlib`)' zlib-libz-1.3.1-gcc
emit examples/libs/zlib/pinned/libz.so.1.3.1-clang-18 ZlibLibz131Clang 'zlib 1.3.1 `libz.so.1.3.1` (Clang 18.1 `-O2`, upstream tarball; `examples/libs/zlib`)' zlib-libz-1.3.1-clang
emit examples/elf/pinned/glibc-libm.so.6 GlibcLibm 'glibc 2.39 `libm.so.6` (Ubuntu libc6 2.39-0ubuntu8.9)' glibc-libm
emit examples/elf/pinned/glibc-libc.so.6 GlibcLibc 'glibc 2.39 `libc.so.6` (Ubuntu libc6 2.39-0ubuntu8.9)' glibc-libc
echo "gen.sh: ok"
