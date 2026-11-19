#!/usr/bin/env bash
# Regenerate (or, with --check, compare) the display listings of Silmaril.Elf.Asm.Example.
set -euo pipefail
cd "$(dirname "$0")/../.."
python3 -I scripts/elf-asm/listing.py \
  examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums \
  Silmaril.Elf.Asm.Example Silmaril/Elf/Asm/Example/Listing.lean \
  crc32Lines=crc32:0x401ac0:7 crc32zLines=crc32_z:0x401990:291 \
  adler32Lines=adler32:0x401880:7 adler32zLines=adler32_z:0x401410:1135 "$@"
python3 -I scripts/elf-asm/listing.py \
  examples/elf-asm/reloc/scaled.o \
  Silmaril.Elf.Asm.Example.Reloc Silmaril/Elf/Asm/Example/Reloc/Listing.lean \
  scaledLines=scaled_plus_bias:0:20 "$@"
python3 -I scripts/elf-asm/listing.py \
  examples/elf-ladder/01-leaf-arith/pinned/leaf-arith \
  Silmaril.Elf.Asm.Example.LeafArith Silmaril/Elf/Asm/Example/LeafArith/Listing.lean \
  clampLines=clamp_i32:0x4013a0:19 satLines=sat_add_u32:0x401400:29 "$@"
