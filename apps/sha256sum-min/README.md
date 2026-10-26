# `sha256sum-min` source and build recipe

`sha256sum-min` is a libc-free reimplementation of GNU coreutils 9.4
`sha256sum` for x86-64 Linux: a GCC 13.3.0 `-O2` driver with the pinned Clang
18.1.3 `-O2` SHA-256 compression bytes. The executable is 35,512 bytes,
SHA-256 `22fa6345cc5bed08f07d4d5a0836885118259a73402470e4d7f7a7a81ad42817`,
and is transcribed in `Silmaril/Apps/Sha256sum/Binary` and
`Silmaril/Process/LPS/Problems/GnuSha256sum/Elf.lean`. It is distinct from the
smaller `apps/sha256-cli` filter and its O3 variants.

This directory is GPLv3 material (it follows coreutils/gnulib/glibc
structure and texts); see [`NOTICES/GPLv3/SHA256SUM-MIN.md`](../../NOTICES/GPLv3/SHA256SUM-MIN.md).

## Contents

- `src/`: the C driver, start-up/system-call assembly, generated GNU
  text/errno tables, compression assembly and pilot hex.
- `scripts/build.sh`, the generators and the pilot byte checker: the original
  build scripts.
- `inputs/xc_sha256.c`: the input used for the GCC-compress sibling, from
  commit `76eb80d5cb83e0396af429f1631b350cb898805e`.
- `historical-manifest.json`: the original build, source and tool-version
  receipt. Every recorded source, generator and input hash matches the files
  here.

The generated `src/gen_tables.h` is part of the frozen program: its
help/version/strerror bytes came from the original GNU/glibc environment.
Regenerating it elsewhere can change observable behaviour.

## Rebuilding

`build.py` verifies every recorded identity, reads the recipe's literal flags,
uses the frozen inputs here and preserves the generated tables:

```sh
python3 apps/sha256sum-min/build.py --verify-only
python3 apps/sha256sum-min/build.py --cc gcc --out /tmp/sha256sum-reproduced
```

Building requires x86-64 GCC 13.3.0 and GNU binutils 2.42, and a fresh output
directory. A build writes both executables and a receipt with compiler and
component hashes, commands, pilot-byte checks and comparisons with the
recorded hashes. The original `scripts/build.sh` takes a source checkout at
the input commit above.

A frozen-input rebuild with GCC 13.3.0 and binutils 2.42 reproduced **both
original executable hashes exactly**, passed the native
compression/relocation/K-byte check, and printed the expected GNU-format stdin
records for empty input and `abc`. Changed source, table, recipe, wrapper
input and pilot-hex controls were rejected. Commands, tool hashes, outputs and
limits are in
[`recovered-provenance.json`](../../scripts/sha256sum/recovered-provenance.json).

The proofs about this executable are listed in
[`docs/projects/sha256sum.md`](../../docs/projects/sha256sum.md).
