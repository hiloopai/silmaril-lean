# Pinned executable

The `-O2` executable built by `../build.sh` (GCC 13.3.0, GNU ld 2.42; flags in
`../../common/flags.sh`), committed so that the Lean transcriptions of its code
(`crc32_z`, `adler32_z`, the `crc32`/`adler32` wrappers and `crc_table`, in
`Silmaril.X86.Ladder.ZlibChecksums`) can be checked against the file. A rebuild with that
toolchain reproduces it byte for byte (`zlib-checksums.sha256`).

Licence: this binary contains object code compiled, unmodified, from zlib 1.3.1 `adler32.c` and
`crc32.c` (with `-DZ_SOLO`), which are under the zlib licence, copied here as `LICENSE.zlib`:
Copyright (C) 1995-2022 Jean-loup Gailly and Mark Adler. The rest (`../main.c`,
`../../common/`) is under this repository's MIT licence.
