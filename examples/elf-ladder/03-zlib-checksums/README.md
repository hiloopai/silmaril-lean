# 03-zlib-checksums

zlib 1.3.1 `adler32.c` and `crc32.c`, compiled unmodified with `-DZ_SOLO`. `fetch-zlib.sh`
downloads the upstream release tarball (SHA-256 checked) and extracts the needed files into
`zlib-1.3.1/`; `zlib-1.3.1.sha256` pins them and `build.sh` checks it. `main.c` checks the
functions against published vectors, a byte-wise reference CRC and the combine laws.

`Silmaril.X86.Ladder.ZlibChecksums` proves, for the `-O2` build (`pinned/zlib-checksums`),
that `crc32_z` and `crc32` compute the CRC-32 of the buffer, and that `adler32_z` and `adler32`
compute zlib's Adler-32, which is RFC 1950's (`Rfc1950.adler32_one_eq_rfc1950`).

Under `Z_SOLO`, `zconf.h` defines neither `Z_U4` nor `Z_U8`, so `z_crc_t` is `unsigned long`
(8-byte table entries) and the braided CRC is compiled out: `crc32_z` is the byte-wise table
loop. `build.sh` also builds a braided variant (`build/braid`, `-DZ_U4=unsigned
-DZ_U8='unsigned long'`, W = 8, N = 5), which is not proved.
