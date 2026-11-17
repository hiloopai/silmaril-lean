# Pinned ELF files of the ELF reader

The files the per-part ELF reader (`Silmaril.Elf.Staged.Pinned.*`,
[docs/projects/elf-reader.md](../../docs/projects/elf-reader.md)) checks and the explorer's ELF
tab shows. The proofs trust only that the bytes are these files: every part is checked by the
kernel on the file's `include_bytes`.

| file | what | size | SHA-256 |
|---|---|---|---|
| `pinned/gnu-sha256sum` | GNU coreutils 9.4 `sha256sum`, `/usr/bin/sha256sum` of Ubuntu `coreutils` 9.4-3ubuntu6.3 (amd64), unmodified: a stripped x86-64 PIE, dynamically linked (glibc, OpenSSL `libcrypto`) | 39336 | `4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60` |
| `pinned/glibc-libc.so.6` | glibc 2.39 `libc.so.6` of Ubuntu `libc6` 2.39-0ubuntu8.9 (amd64), unmodified, stripped (`.dynsym` only) | 2129424 | `3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf` |
| `pinned/glibc-libm.so.6` | glibc 2.39 `libm.so.6`, same package | 952616 | `fce00b6f25f459cf4ae0b7fae4257909a1a8a86f9149e7c029a5d617baf1ccd0` |
| `pinned/zlib-libz.so.1.3` | zlib 1.3 `libz.so.1.3` of Ubuntu `zlib1g` 1:1.3.dfsg-3.1ubuntu2.3 (amd64), unmodified, stripped | 113000 | `f61677c7bdb7c2aa2a243ea781bfd16afcb361cede7b4ef76127a9d8eb9a5242` |
| `../elf-ladder/01-leaf-arith/pinned/leaf-arith` | the leaf functions of `examples/elf-ladder/01-leaf-arith/arith.c` with a test driver, GCC 13.3 `-O2`, static, not stripped (`.symtab`); built by `examples/elf-ladder/01-leaf-arith/build.sh`; the code of the ABI conformance example ([docs/projects/abi-conformance.md](../../docs/projects/abi-conformance.md)) | 9632 | `d9cf1e5ddd99bcb2abeca7ae44f899c03bbd93586458a7367e1ff6d4a6472484` |
| `../elf-ladder/03-zlib-checksums/pinned/zlib-checksums` | zlib 1.3.1 `adler32.c` and `crc32.c` with a test driver, GCC 13.3 `-O2`, static, not stripped (`.symtab`); built by `examples/elf-ladder/03-zlib-checksums/build.sh` | 12224 | `eeb7934b8c5a13b6fb98ee1a3a15dd2e6861436a6502544dcc549695c39df343` |
| `../dyn/pinned/hello-gcc` | hello world (`examples/dyn/hello/hello.c`), gcc 13.3 `-O2`, dynamically linked against glibc 2.39 (`PT_INTERP` `/lib64/ld-linux-x86-64.so.2`, `DT_NEEDED` `libc.so.6`); pinned and reproducible: [examples/dyn](../dyn/README.md) | 15960 | `6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7` |
| `../dyn/pinned/hello-clang` | the same hello world, clang 18.1 `-O2`, dynamically linked against glibc 2.39 (same interpreter and `DT_NEEDED`); pinned and reproducible as above | 16008 | `ecad1a19e6e63e4828e9386a9c831dc6beb635c6858dc42d2c248e6397eaa713` |

    examples/elf/pin.sh --check   # the committed files have the pinned SHA-256
    examples/elf/pin.sh --fetch   # download the Ubuntu package, check it, extract sha256sum

`--fetch` downloads `coreutils_9.4-3ubuntu6.3_amd64.deb` from Launchpad
(`https://launchpad.net/ubuntu/+archive/primary/+files/coreutils_9.4-3ubuntu6.3_amd64.deb`,
falling back to `archive.ubuntu.com`), checks its SHA-256
(`e1e9a17892be0cc83b7cea747edf331ffeb6d6c010b4db296e60d888e8e9274c`), extracts
`./usr/bin/sha256sum` and checks the file's SHA-256. It is the same file whose functions
`Silmaril.Elf.Effects.Example.Sha256sum` certifies (`NOTICES/effects-examples`).

`--fetch` also downloads `libc6_2.39-0ubuntu8.9_amd64.deb` (sha256
`ff5557d99b51f761c4b7c92368b9cc45565eda17df9bf9eb4b134d09825008be`) and
`zlib1g_1.3.dfsg-3.1ubuntu2.3_amd64.deb` (sha256
`376249c8de139568221dbb242318cc8cb8f02299e3a62b7432948e1754fbddf9`) from Launchpad and checks each
package and file. Licences and corresponding source: `NOTICES/glibc` (LGPL-2.1-or-later) and
`NOTICES/zlib` (zlib licence).

`disasm/*.objdump` are the listings the explorer shows as **unverified** disassembly: GNU
objdump's output (`objdump -d -w -z FILE`; the first line records the objdump version), written by
`scripts/elf-reader/gen.sh`, for files up to 512 KiB; the glibc libraries are disassembled by
`elf-pages` when it writes the pages (with the objdump version recorded). Nothing in Lean is about
them.

## Licence

GNU coreutils is licensed under the GNU General Public License, version 3 or (at your option) any
later version (`NOTICES/GPLv3`). The corresponding source of this binary is
https://launchpad.net/ubuntu/+source/coreutils/9.4-3ubuntu6.3 (and https://ftp.gnu.org/gnu/coreutils/);
see `NOTICES/effects-examples`. The file is redistributed unmodified.
