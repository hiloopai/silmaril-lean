# zlib 1.3.1 shared libraries, built by GCC and by Clang

`pinned/libz.so.1.3.1-gcc-13` and `pinned/libz.so.1.3.1-clang-18` are zlib 1.3.1's shared
library, built from the release tarball (SHA-256
`9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23`) by `./configure && make
libz.so.1.3.1` with `CFLAGS='-O2 -ffile-prefix-map=/build/zlib-1.3.1=.'`. They are files of the
ABI conformance library matrix ([docs/projects/abi-conformance.md](../../../docs/projects/abi-conformance.md),
`Silmaril.Elf.Abi.ZlibMatrix`) and of the ELF reader (`Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc`,
`…ZlibLibz131Clang`).

    examples/libs/zlib/build.sh           # build into pinned/ (docker)
    examples/libs/zlib/build.sh --check   # rebuild and compare byte for byte

The build runs in `ubuntu:24.04` pinned by digest. `container.sh` installs the toolchain at
fixed versions from the Ubuntu snapshot archive (`20261116T000000Z`): GCC 13.3.0-6ubuntu2~24.04.1,
Clang 1:18.1.3-1ubuntu1, binutils 2.42-4ubuntu2.10, glibc 2.39-0ubuntu8.12. It builds at a fixed
path, with fixed `SOURCE_DATE_EPOCH`, locale, time zone and umask. `pinned/packages-*.txt` lists
the installed versions, and `pinned/build-*.log` holds each build's output.

| file | SHA-256 | size |
| --- | --- | --- |
| `pinned/libz.so.1.3.1-gcc-13` | `cc4d841d56109a1c8f2271a6c33e304128aee44e7e822f81458e3b4f82f160c8` | 109432 |
| `pinned/libz.so.1.3.1-clang-18` | `d4e99da347fa22efa759cbb2f9fa47d9199ff898e6927841bb4543d0c21f83a6` | 117200 |

`build.sh --check` reproduced both files byte for byte in a second, independent container run.

Licence: zlib licence (`NOTICES/zlib`).
