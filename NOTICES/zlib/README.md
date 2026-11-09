# zlib 1.3.1

`examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums` and the byte literals of
`Silmaril.X86.Ladder.ZlibChecksums` (the code of `crc32_z`, `crc32`, `adler32_z`, `adler32` and
the `crc_table` contents) are object code and data compiled, unmodified, from zlib 1.3.1
`adler32.c` and `crc32.c` (release tarball SHA-256
`9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23`). They are under the zlib
licence, reproduced in `LICENSE`: Copyright (C) 1995-2022 Jean-loup Gailly and Mark Adler. The
zlib sources themselves are not in this repository; `fetch-zlib.sh` downloads them.
