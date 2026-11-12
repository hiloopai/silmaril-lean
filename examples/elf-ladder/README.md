# ELF ladder: the rungs with Lean proofs

Small, freestanding, statically linked x86-64 Linux programs whose code is proved in
`Silmaril.X86.Ladder`. Each binary tests itself and exits 0 on success. Three rungs are here:

| rung | subject | Lean |
|---|---|---|
| `01-leaf-arith` | `arith.c` (`sat_add_u32`, `bswap32_manual`, `clamp_i32`, `gcd_u32`, and three unproved leaves) | `Silmaril.X86.Ladder.LeafArith.Thms`, `Silmaril.X86.AbiFunction.LeafArith.Thms` |
| `02-mem-loops` | `common/libmini.c` (`memcpy`, `memmove`, `memset`, `memcmp`, `strlen`) | `Silmaril.X86.Ladder.LibMini.Thms` (`memcpy`, `memset`, `strlen`) |
| `03-zlib-checksums` | zlib 1.3.1 `adler32.c`, `crc32.c`, compiled unmodified with `-DZ_SOLO` | `Silmaril.X86.Ladder.ZlibChecksums.Thms` (`adler32_z`, `adler32`, `crc32_z`, `crc32`) |

The Lean modules transcribe the code of the `-O2` executables as byte literals. Each module's
header names the executable, the address and the SHA-256 of the file.

## Building

Toolchain: GCC 13.3.0 and GNU binutils 2.42 (Ubuntu 24.04: `gcc 13.3.0-6ubuntu2~24.04.1`,
`binutils 2.42`). The flags are in `common/flags.sh`. Each rung is built at `-O1` and `-O2`
into `<rung>/build/` (git-ignored) and run once:

```sh
bash 01-leaf-arith/build.sh
bash 02-mem-loops/build.sh
bash 03-zlib-checksums/fetch-zlib.sh   # zlib 1.3.1 sources, checked by SHA-256
bash 03-zlib-checksums/build.sh
```

## Pinned executables

The `-O2` executables are committed under `<rung>/pinned/` with their `.sha256`, so the
transcriptions can be checked against the files without a build. With the toolchain above the
build reproduces them byte for byte:

```sh
cmp 01-leaf-arith/build/O2/leaf-arith 01-leaf-arith/pinned/leaf-arith
cmp 02-mem-loops/build/O2/mem-loops 02-mem-loops/pinned/mem-loops
cmp 03-zlib-checksums/build/O2/zlib-checksums 03-zlib-checksums/pinned/zlib-checksums
(cd 01-leaf-arith/pinned && sha256sum -c leaf-arith.sha256)
(cd 02-mem-loops/pinned && sha256sum -c mem-loops.sha256)
(cd 03-zlib-checksums/pinned && sha256sum -c zlib-checksums.sha256)
```

`Silmaril.X86.Ladder.Pinned.Thms` (rung 01: `Pinned.LeafArith.Thms`) proves that the Lean byte literals are the bytes these files
load at the stated addresses: it runs the public LPS loader (`ELFImage.parse`) on the files,
embedded as `Silmaril.X86.Link.Blob` literals in `Silmaril/X86/Ladder/Pinned/<Rung>.lean`, by
kernel evaluation. `pin.sh` regenerates those modules from the pinned files, and
`pin.sh --check` checks that they match the files and their `.sha256` (coreutils only):

```sh
bash pin.sh --check
```

## Licences

`common/`, `01-leaf-arith/arith.{c,h}`, the drivers (`main.c`) and the scripts are under this
repository's MIT licence.
`03-zlib-checksums/pinned/zlib-checksums` contains object code compiled, unmodified, from zlib
1.3.1, which is under the zlib licence (`03-zlib-checksums/pinned/LICENSE.zlib`; see
`NOTICES/zlib`).
