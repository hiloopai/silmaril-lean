# zlib 1.3.1

`examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums` and the byte literals of
`Silmaril.X86.Ladder.ZlibChecksums` (the code of `crc32_z`, `crc32`, `adler32_z`, `adler32` and
the `crc_table` contents) are object code and data compiled, unmodified, from zlib 1.3.1
`adler32.c` and `crc32.c` (release tarball SHA-256
`9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23`). They are under the zlib
licence, reproduced in `LICENSE`: Copyright (C) 1995-2022 Jean-loup Gailly and Mark Adler. The
zlib sources themselves are not in this repository; `fetch-zlib.sh` downloads them.

## zlib 1.3 `libz.so.1.3` (Ubuntu)

`examples/elf/pinned/zlib-libz.so.1.3` is `/usr/lib/x86_64-linux-gnu/libz.so.1.3` of Ubuntu
`zlib1g` 1:1.3.dfsg-3.1ubuntu2.3 (amd64), redistributed unmodified (113000 bytes, sha256
`f61677c7bdb7c2aa2a243ea781bfd16afcb361cede7b4ef76127a9d8eb9a5242`; `examples/elf/pin.sh
--fetch`). It is under the zlib licence (`LICENSE`); its source is
https://launchpad.net/ubuntu/+source/zlib/1:1.3.dfsg-3.1ubuntu2.3.

## zlib 1.2.11 `libz.so.1.2.11` (Ubuntu)

`examples/elf/pinned/zlib-libz.so.1.2.11` is `/lib/x86_64-linux-gnu/libz.so.1.2.11` of Ubuntu
22.04 `zlib1g` 1:1.2.11.dfsg-2ubuntu9.2 (amd64), redistributed unmodified (108936 bytes, sha256
`64c206f0146cc58bbddc4f22054436f4ff278f5a554aa3ce6921ddf7e9133370`; `examples/elf/pin.sh
--fetch`). It is under the zlib licence (`LICENSE`); its source is
https://launchpad.net/ubuntu/+source/zlib/1:1.2.11.dfsg-2ubuntu9.2.

## zlib 1.3.1 `libz.so.1.3.1` (GCC and Clang builds)

`examples/libs/zlib/pinned/libz.so.1.3.1-gcc-13` and `…-clang-18` are zlib 1.3.1's shared library
compiled, unmodified, from the release tarball above by `examples/libs/zlib/build.sh` (GCC 13.3
and Clang 18.1, `-O2`). They are under the zlib licence (`LICENSE`); their source is the release
tarball, https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz.
