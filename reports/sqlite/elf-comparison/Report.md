# SQLite 3.54.1 ELF comparison

Eight x86-64 Linux SysV glibc shared-library builds compare GCC and Clang at `-O0`, `-O1`, `-O2`, and `-O3`. The baseline is `gcc-O2`. Every pair shares 274 defined dynamic function names.

**GCC vs. Clang at `-O2`.** Exact symbol labels give 1,324 unambiguous pairs out of 1,609 GCC spans and 1,602 Clang spans. 53 pairs have identical function bytes, covering 279 bytes out of 721,879 GCC and 813,576 Clang matched function bytes. The normalized signatures agree in 79/854 eligible pairs, including 26 with different bytes. The CFGs share 24,355/61,453 · 24,355/73,596 typed edges among mutually eligible pairs. The call graphs share 3,258 distinct edges out of 5,462 GCC and 4,819 Clang edges among mutually matched, decoded callers. Use these results as structural discovery evidence only.

## Provenance and replay

- SQLite source ID `2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`. [Upstream release](https://sqlite.org/releaselog/3_54_1.html) · [Pinned amalgamation ZIP](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip)
- ZIP SHA-256 `0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`. ZIP SHA3-256 `92281c86e2957f9b9305890f9ac04204caa7b677cc868dc326d942689df28e30`.
- `sqlite3.c` SHA-256 `0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`. `sqlite3.h` SHA-256 `d6c84557261893439b341d2e6c35187ae3ea24fbfd843ad94616f72d89242b8c`.
- gcc (Debian 14.2.0-19) 14.2.0 and Debian clang version 19.1.7 (3+b1). GNU ld (GNU Binutils for Debian) 2.44, glibc 2.41, and rustc 1.85.1 (4eb161250 2025-03-15) (built from a source tarball).
- The amalgamation builds with fixed SQLite options and `-fno-builtin` on both drivers. Explicit compiler built-ins in the source and compiler predefines follow the selected compiler. Each run records the full sorted preprocessor dump and its SHA-256. Runtime compile options agree across the matrix after removing the compiler identification string.
- Each object links twice. `libsqlite3.so` is the ordinary unstripped link. `stripped.so` comes from that link via GNU `strip --strip-all`. `relocs.so` comes from a link with `--emit-relocs` and supplies the retained text relocations. All three agree on executable load segment addresses, sizes and hashes, dynamic symbol records after resolving section indices, dynamic linking metadata and loader relocations. The runtime pair shares a build ID. The analysis link carries its own build ID and agrees with the ordinary link on usable symbol slices.
- SONAME `libsqlite3.so.0` and DT_NEEDED entries `libm.so.6`, `libc.so.6` for the baseline. JSON records each build.

The baseline commands run in the build-specific directory under `$WORK` with `LC_ALL=C`, `TZ=UTC`, and `SOURCE_DATE_EPOCH=0`.

```sh
gcc -O2 -m64 -march=x86-64 -mtune=generic -fPIC -fno-builtin -fno-lto -pthread -g -gdwarf-4 "-ffile-prefix-map=$WORK=." "-fdebug-prefix-map=$WORK=." -DSQLITE_THREADSAFE=1 -DSQLITE_OMIT_LOAD_EXTENSION=1 -DSQLITE_MAX_MMAP_SIZE=0 -DSQLITE_DEFAULT_MMAP_SIZE=0 -c ../source/sqlite3.c -o sqlite3.o
gcc -m64 -fno-lto -pthread -fuse-ld=bfd -shared -Wl,--as-needed,--build-id=sha1,-soname,libsqlite3.so.0 -o libsqlite3.so sqlite3.o -lm
gcc -m64 -fno-lto -pthread -fuse-ld=bfd -shared -Wl,--emit-relocs -Wl,--as-needed,--build-id=sha1,-soname,libsqlite3.so.0 -o relocs.so sqlite3.o -lm
strip --strip-all -o stripped.so libsqlite3.so
```

The standalone recipe, package versions, measurement definitions and schema are in the repository. [Generator and methodology](README.md) · [Measured data](results.json) · [JSON schema](results.schema.json)

## ELF inventory

| Build | Func records | Zero size | Usable spans | Usable bytes | Alias spans | Clone labels | Split/outline labels | Inline DIEs | Normalized coverage |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `gcc-O0` | 2,615 | 6 | 2,609 | 967,399 | 0 | 0 | 0 | 23 | 2,208/2,609 |
| `gcc-O1` | 1,967 | 6 | 1,961 | 652,699 | 0 | 0 | 0 | 1,131 | 1,618/1,961 |
| `gcc-O2` | 1,618 | 6 | 1,609 | 851,219 | 3 | 163 | 81 | 9,311 | 1,162/1,609 |
| `gcc-O3` | 1,469 | 6 | 1,460 | 1,205,167 | 3 | 153 | 78 | 13,571 | 957/1,460 |
| `clang-O0` | 2,615 | 6 | 2,609 | 901,631 | 0 | 0 | 0 | 23 | 2,212/2,609 |
| `clang-O1` | 1,617 | 6 | 1,611 | 935,381 | 0 | 0 | 0 | 12,727 | 1,116/1,611 |
| `clang-O2` | 1,608 | 6 | 1,602 | 964,565 | 0 | 0 | 0 | 12,860 | 1,087/1,602 |
| `clang-O3` | 1,601 | 6 | 1,595 | 1,062,589 | 0 | 0 | 0 | 13,921 | 1,067/1,595 |

SHA-256 values for the ordinary and stripped runtime files are below. The JSON includes sizes, analysis ELF, object and macro dump digests and both build IDs.

| Build | Ordinary SHA-256 | Stripped SHA-256 |
| --- | --- | --- |
| `gcc-O0` | `a38b26c31767068ac2867be98c505bb049320c01b973c45cc843ed5d66db6e7f` | `202ced6e7c7152fde88754c08e9049e0aeba065e1ac4ea403083c0c65fdff01f` |
| `gcc-O1` | `9d40fe473528c715f72c32bec30b58ef70dd47d9b7f868f1809dfe22999e5021` | `58270e04fb462061df3ae25a0b6ace1cf7bfc15e4fd55b5b28b2b8e8f0c9e8d3` |
| `gcc-O2` | `31d32767089dadc634fc6b07f5975fe8371a2c2d5765e35cea6fe0a82166ac06` | `139d69780ea544eab99979c69f71ce2c011fe1dfb990eb94f029ca77207e5808` |
| `gcc-O3` | `6be1945ba8e629dc5ebee1825bc3ac5f5c7638eb75d5e3ecc51e377e465cf43a` | `f9211fdba715b1c3640652faf2acbd999054779d4daec45a2b9f1b977c324eec` |
| `clang-O0` | `6fa7ae4e8a2c4bfa41e95d958dd5715ed455d1cff239afc7def0dd0b167c573c` | `67f556b82f07a1e71f01b1f2c104eb0772819f6cea8508d2084d5f0f25e285e9` |
| `clang-O1` | `eb156f98448b6c503c45d6b98ffe34551bb267b86ef500eb58c298cda90656b0` | `26c80b9a9ee45fe709845962e8411571a5fa73307cd98457f6d33f198e3f9dcf` |
| `clang-O2` | `9b61e3043068618f03016f856ac61f3ff2a5ecbf029864e6ab38934bf1804d37` | `8a8e49255a297d0e04b834381f70b8c9f5c9b7ea75394caaf62895f5a9912db2` |
| `clang-O3` | `85a617c4506dd37d77ca874ab459599bc052299bf22b4addbcf9a8a620d63daf` | `2bd72a74d7200b7abdedfdd420ee09a661910fddf7e0e385a1094fb7e022fc40` |

## Symbol and byte overlap

Each directional fraction shares a numerator and uses the left or right build as its denominator. Ambiguous and unmatched counts are ordered left then right. Exact compares complete symbol slices among unambiguous pairs. Normalized divides by pairs with a signature on both sides.

| Pair (left / right) | Symbol names L · R | Matched spans L · R | Ambiguous L / R | Unmatched L / R | Exact / matched | Normalized / eligible | Normalized only |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `gcc-O0` / `gcc-O1` | 1,961/2,609 · 1,961/1,961 | 1,961/2,609 · 1,961/1,961 | 0 / 0 | 648 / 0 | 0/1,961 | 0/1,616 | 0 |
| `gcc-O0` / `gcc-O2` | 1,449/2,609 · 1,449/1,612 | 1,443/2,609 · 1,443/1,609 | 6 / 3 | 1160 / 163 | 0/1,443 | 0/1,031 | 0 |
| `gcc-O0` / `gcc-O3` | 1,310/2,609 · 1,310/1,463 | 1,304/2,609 · 1,304/1,460 | 6 / 3 | 1299 / 153 | 0/1,304 | 0/845 | 0 |
| `gcc-O0` / `clang-O0` | 2,609/2,609 · 2,609/2,609 | 2,609/2,609 · 2,609/2,609 | 0 / 0 | 0 / 0 | 43/2,609 | 51/2,204 | 8 |
| `gcc-O0` / `clang-O1` | 1,611/2,609 · 1,611/1,611 | 1,611/2,609 · 1,611/1,611 | 0 / 0 | 998 / 0 | 0/1,611 | 0/1,113 | 0 |
| `gcc-O0` / `clang-O2` | 1,602/2,609 · 1,602/1,602 | 1,602/2,609 · 1,602/1,602 | 0 / 0 | 1007 / 0 | 0/1,602 | 0/1,084 | 0 |
| `gcc-O0` / `clang-O3` | 1,595/2,609 · 1,595/1,595 | 1,595/2,609 · 1,595/1,595 | 0 / 0 | 1014 / 0 | 0/1,595 | 0/1,064 | 0 |
| `gcc-O1` / `gcc-O2` | 1,435/1,961 · 1,435/1,612 | 1,429/1,961 · 1,429/1,609 | 6 / 3 | 526 / 177 | 35/1,429 | 52/1,026 | 17 |
| `gcc-O1` / `gcc-O3` | 1,295/1,961 · 1,295/1,463 | 1,289/1,961 · 1,289/1,460 | 6 / 3 | 666 / 168 | 35/1,289 | 50/838 | 15 |
| `gcc-O1` / `clang-O0` | 1,961/1,961 · 1,961/2,609 | 1,961/1,961 · 1,961/2,609 | 0 / 0 | 0 / 648 | 0/1,961 | 0/1,615 | 0 |
| `gcc-O1` / `clang-O1` | 1,530/1,961 · 1,530/1,611 | 1,530/1,961 · 1,530/1,611 | 0 / 0 | 431 / 81 | 29/1,530 | 35/1,062 | 6 |
| `gcc-O1` / `clang-O2` | 1,520/1,961 · 1,520/1,602 | 1,520/1,961 · 1,520/1,602 | 0 / 0 | 441 / 82 | 29/1,520 | 35/1,033 | 6 |
| `gcc-O1` / `clang-O3` | 1,512/1,961 · 1,512/1,595 | 1,512/1,961 · 1,512/1,595 | 0 / 0 | 449 / 83 | 29/1,512 | 34/1,017 | 5 |
| `gcc-O2` / `gcc-O3` | 1,400/1,612 · 1,400/1,463 | 1,397/1,609 · 1,397/1,460 | 0 / 0 | 212 / 63 | 163/1,397 | 472/908 | 309 |
| `gcc-O2` / `clang-O0` | 1,449/1,612 · 1,449/2,609 | 1,443/1,609 · 1,443/2,609 | 3 / 6 | 163 / 1160 | 0/1,443 | 0/1,030 | 0 |
| `gcc-O2` / `clang-O1` | 1,331/1,612 · 1,331/1,611 | 1,331/1,609 · 1,331/1,611 | 0 / 0 | 278 / 280 | 53/1,331 | 79/875 | 26 |
| `gcc-O2` / `clang-O2` | 1,324/1,612 · 1,324/1,602 | 1,324/1,609 · 1,324/1,602 | 0 / 0 | 285 / 278 | 53/1,324 | 79/854 | 26 |
| `gcc-O2` / `clang-O3` | 1,314/1,612 · 1,314/1,595 | 1,314/1,609 · 1,314/1,595 | 0 / 0 | 295 / 281 | 53/1,314 | 79/841 | 26 |
| `gcc-O3` / `clang-O0` | 1,310/1,463 · 1,310/2,609 | 1,304/1,460 · 1,304/2,609 | 3 / 6 | 153 / 1299 | 0/1,304 | 0/845 | 0 |
| `gcc-O3` / `clang-O1` | 1,259/1,463 · 1,259/1,611 | 1,259/1,460 · 1,259/1,611 | 0 / 0 | 201 / 352 | 53/1,259 | 68/773 | 15 |
| `gcc-O3` / `clang-O2` | 1,256/1,463 · 1,256/1,602 | 1,256/1,460 · 1,256/1,602 | 0 / 0 | 204 / 346 | 53/1,256 | 68/756 | 15 |
| `gcc-O3` / `clang-O3` | 1,245/1,463 · 1,245/1,595 | 1,245/1,460 · 1,245/1,595 | 0 / 0 | 215 / 350 | 54/1,245 | 68/745 | 14 |
| `clang-O0` / `clang-O1` | 1,611/2,609 · 1,611/1,611 | 1,611/2,609 · 1,611/1,611 | 0 / 0 | 998 / 0 | 0/1,611 | 0/1,114 | 0 |
| `clang-O0` / `clang-O2` | 1,602/2,609 · 1,602/1,602 | 1,602/2,609 · 1,602/1,602 | 0 / 0 | 1007 / 0 | 0/1,602 | 0/1,085 | 0 |
| `clang-O0` / `clang-O3` | 1,595/2,609 · 1,595/1,595 | 1,595/2,609 · 1,595/1,595 | 0 / 0 | 1014 / 0 | 0/1,595 | 0/1,065 | 0 |
| `clang-O1` / `clang-O2` | 1,594/1,611 · 1,594/1,602 | 1,594/1,611 · 1,594/1,602 | 0 / 0 | 17 / 8 | 171/1,594 | 528/1,081 | 357 |
| `clang-O1` / `clang-O3` | 1,569/1,611 · 1,569/1,595 | 1,569/1,611 · 1,569/1,595 | 0 / 0 | 42 / 26 | 155/1,569 | 396/1,049 | 241 |
| `clang-O2` / `clang-O3` | 1,577/1,602 · 1,577/1,595 | 1,577/1,602 · 1,577/1,595 | 0 / 0 | 25 / 18 | 199/1,577 | 645/1,047 | 446 |

For the `-O2` cross-compiler pair, the GCC and Clang unmatched counts are 285 and 278. Of these, 111 and 55 have only a clone-name hint, 142 and 172 have only a DWARF inline hint, 32 and 51 have both, and 0 and 0 have neither. These counts describe labels and debug annotations.

## Control flow and direct call graph

CFGs compare typed edges between address-order block ordinals and typed exits. The direct call graph uses exact-symbol matched callers and resolved target labels. Directional denominators in this table are limited to pairs eligible on both sides. The JSON also carries each build's full CFG and call-edge denominators.

| Pair (left / right) | Equal CFG / eligible | Shared CFG edges L · R | Shared direct call edges L · R |
| --- | --- | --- | --- |
| `gcc-O0` / `gcc-O1` | 430/1,961 | 15,564/43,071 · 15,564/48,971 | 6,836/7,614 · 6,836/8,039 |
| `gcc-O0` / `gcc-O2` | 151/1,443 | 15,730/37,403 · 15,730/65,116 | 3,117/6,739 · 3,117/5,751 |
| `gcc-O0` / `gcc-O3` | 133/1,304 | 15,420/35,969 · 15,420/91,919 | 2,454/6,386 · 2,454/6,137 |
| `gcc-O0` / `clang-O0` | 1,273/2,609 | 26,160/53,424 · 26,160/56,517 | 9,377/9,381 · 9,377/9,395 |
| `gcc-O0` / `clang-O1` | 123/1,611 | 17,616/42,465 · 17,616/88,519 | 2,752/7,700 · 2,752/5,871 |
| `gcc-O0` / `clang-O2` | 123/1,602 | 17,131/42,024 · 17,131/87,050 | 2,695/7,633 · 2,695/5,774 |
| `gcc-O0` / `clang-O3` | 115/1,595 | 16,876/41,821 · 16,876/95,654 | 2,730/7,605 · 2,730/5,834 |
| `gcc-O1` / `gcc-O2` | 180/1,429 | 17,635/42,307 · 17,635/63,867 | 3,481/6,953 · 3,481/5,581 |
| `gcc-O1` / `gcc-O3` | 161/1,289 | 16,370/40,036 · 16,370/87,775 | 2,693/6,560 · 2,693/5,917 |
| `gcc-O1` / `clang-O0` | 428/1,961 | 14,581/48,971 · 14,581/45,597 | 6,833/8,039 · 6,833/7,621 |
| `gcc-O1` / `clang-O1` | 136/1,530 | 17,253/45,046 · 17,253/82,103 | 2,724/7,530 · 2,724/5,353 |
| `gcc-O1` / `clang-O2` | 138/1,520 | 16,937/44,609 · 16,937/80,944 | 2,665/7,472 · 2,665/5,286 |
| `gcc-O1` / `clang-O3` | 131/1,512 | 16,943/44,443 · 16,943/89,245 | 2,692/7,449 · 2,692/5,342 |
| `gcc-O2` / `gcc-O3` | 609/1,397 | 36,471/67,089 · 36,471/97,495 | 4,437/5,856 · 4,437/6,552 |
| `gcc-O2` / `clang-O0` | 151/1,443 | 15,203/65,116 · 15,203/39,629 | 3,116/5,751 · 3,116/6,748 |
| `gcc-O2` / `clang-O1` | 176/1,331 | 24,585/62,151 · 24,585/74,760 | 3,321/5,533 · 3,321/4,900 |
| `gcc-O2` / `clang-O2` | 180/1,324 | 24,355/61,453 · 24,355/73,596 | 3,258/5,462 · 3,258/4,819 |
| `gcc-O2` / `clang-O3` | 172/1,314 | 24,496/61,193 · 24,496/81,143 | 3,058/5,436 · 3,058/4,866 |
| `gcc-O3` / `clang-O0` | 135/1,304 | 15,084/91,919 · 15,084/38,054 | 2,453/6,137 · 2,453/6,393 |
| `gcc-O3` / `clang-O1` | 136/1,259 | 28,347/88,334 · 28,347/73,397 | 3,035/5,965 · 3,035/4,715 |
| `gcc-O3` / `clang-O2` | 138/1,256 | 28,065/87,841 · 28,065/72,609 | 3,015/5,926 · 3,015/4,662 |
| `gcc-O3` / `clang-O3` | 135/1,245 | 29,202/87,415 · 29,202/79,939 | 3,036/5,896 · 3,036/4,705 |
| `clang-O0` / `clang-O1` | 123/1,611 | 17,291/44,908 · 17,291/88,519 | 2,753/7,713 · 2,753/5,871 |
| `clang-O0` / `clang-O2` | 123/1,602 | 16,853/44,446 · 16,853/87,050 | 2,696/7,644 · 2,696/5,774 |
| `clang-O0` / `clang-O3` | 116/1,595 | 16,748/44,239 · 16,748/95,654 | 2,731/7,616 · 2,731/5,834 |
| `clang-O1` / `clang-O2` | 739/1,594 | 45,386/87,484 · 45,386/86,812 | 5,673/5,773 · 5,673/5,758 |
| `clang-O1` / `clang-O3` | 520/1,569 | 41,607/86,817 · 41,607/94,784 | 5,212/5,721 · 5,212/5,786 |
| `clang-O2` / `clang-O3` | 828/1,577 | 53,359/86,430 · 53,359/95,026 | 5,302/5,721 · 5,302/5,802 |

## Machine idioms and unresolved sites

Site counts cover fully decoded function spans. Each unknown column divides by all sites of the same kind in that build. GOT-labelled indirect sites still depend on dynamic binding. The switch detector recognises one relative jump-table idiom with two inspected entries. Those candidates stay unresolved in the graph. Mutex and helper columns count labelled transfers including calls and jumps. The JSON lists the observed mutex and helper target labels.

| Build | Instructions | CFG coverage | Unknown direct calls | Unresolved indirect calls | Unresolved indirect jumps | Table candidates | LOCK prefix | MFENCE | Memory XCHG | Mutex transfers | Helper transfers |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `gcc-O0` | 253,881 | 2,609/2,609 | 0/13,439 | 254/254 | 41/41 | 0 | 1 | 0 | 0 | 293 | 0 |
| `gcc-O1` | 166,321 | 1,961/1,961 | 0/12,889 | 262/262 | 46/46 | 41 | 5 | 0 | 0 | 309 | 0 |
| `gcc-O2` | 212,322 | 1,609/1,609 | 0/11,139 | 592/592 | 84/84 | 42 | 5 | 0 | 0 | 367 | 0 |
| `gcc-O3` | 289,076 | 1,460/1,460 | 0/13,303 | 979/979 | 97/97 | 49 | 7 | 0 | 0 | 450 | 0 |
| `clang-O0` | 231,804 | 2,609/2,609 | 0/13,463 | 254/254 | 52/52 | 52 | 0 | 1 | 0 | 293 | 0 |
| `clang-O1` | 241,632 | 1,611/1,611 | 0/9,772 | 1,913/1,913 | 148/148 | 54 | 0 | 77 | 0 | 6 | 0 |
| `clang-O2` | 245,876 | 1,602/1,602 | 0/9,732 | 1,901/1,901 | 133/133 | 49 | 0 | 77 | 0 | 6 | 0 |
| `clang-O3` | 267,421 | 1,595/1,595 | 0/10,129 | 2,594/2,594 | 182/182 | 51 | 0 | 81 | 0 | 6 | 0 |

Baseline split or outline label examples include `adjustOrderByCol.part.0`, `btreeReleaseAllCursorPages.part.0`, `codeCompare.part.0.isra.0`, `codeReal.part.0`, `computeJD.part.0`, `computeYMD.part.0`.

## Independently checked sample

Each build cell shows bytes, blocks and distinct direct callees in that order.

| Function | GCC -O2 | Clang -O2 | Exact bytes | Normalized |
| --- | --- | --- | --- | --- |
| `pthreadMutexEnter` | 5 B / 1 / 0 | 5 B / 1 / 0 | different | equal |
| `sqlite3VdbeExec` | 42,343 B / 1,973 / 139 | 49,852 B / 2,561 / 161 | different | unavailable |
| `sqlite3_libversion_number` | 6 B / 1 / 0 | 6 B / 1 / 0 | equal | equal |
| `sqlite3_mutex_enter` | 17 B / 4 / 0 | 12 B / 3 / 0 | different | different |
| `sqlite3_step` | 4,492 B / 225 / 28 | 4,385 B / 281 / 26 | different | unavailable |
| `sqlite3_str_length` | 11 B / 3 / 0 | 12 B / 3 / 0 | different | different |
| `sqlite3_threadsafe` | 6 B / 1 / 0 | 6 B / 1 / 0 | equal | equal |
| `unixShmBarrier` | 38 B / 1 / 1 | 43 B / 4 / 0 | different | different |

- `sqlite3_libversion_number` has the six bytes `b8b1992e00c3` in both builds, a move of 3054001 into EAX followed by return.
- `sqlite3_str_length` has bytes `31c04885ff74038b4718c3` in GCC and `4885ff74048b4718c331c0c3` in Clang.
- `pthreadMutexEnter` reaches the same versioned `pthread_mutex_lock` PLT label via a direct tail jump in both builds. The bytes differ and the normalized signatures agree.
- `sqlite3VdbeExec` has 2 GCC and 5 Clang relative table candidates. The first reported GCC jump is at `0xac432`. The verifier independently decoded two signed table entries and checked both against GNU objdump instruction boundaries.
- `unixShmBarrier` has LOCK/MFENCE counts 1/0 in GCC and 0/1 in Clang. GNU objdump cross-checked both counts.

## Verification and limits

- Two clean build directories agreed byte-for-byte on all 40 manifested files and produced identical analyzer JSON.
- GNU readelf checked symbol counts, loader metadata, build IDs and sample text relocations. GNU objdump checked 64 symbol slices and their transfer site counts. LLVM objdump independently checked 24 small slices. The verifier checked two entries in each of 21 example tables and cross-checked DWARF inline DIE totals for both `-O2` builds.
- 16 ordinary and stripped ELFs passed isolated native smoke tests for version, source ID, thread-safe mode, absent external-loading APIs, file-backed mmap staying at zero, and a small SQL aggregate.
- Scope is one release, one configuration, one target and one version of each compiler. The function universe depends on unstripped symbols, and linear decoding can include padding or miss code outside those symbol spans. Alias and clone labels, DWARF inline sites and calls via PLT/GOT carry compiler or dynamic-linker conventions. CFGs omit jump-table successors and approximate edges after calls as fallthrough. Data contents, interposition, provenance of optimized functions and behavioral equivalence require separate analysis.

## References

- [SQLite compile-time options](https://sqlite.org/compile.html) · [SQLite mmap pragma](https://sqlite.org/pragma.html#pragma_mmap_size)
- [AMD64 System V ABI](https://gitlab.com/x86-psABIs/x86-64-ABI) · [ELF generic ABI](https://gabi.xinuos.com/) · [DWARF 4 specification](https://dwarfstd.org/dwarf4std.html)
- [Rust object](https://docs.rs/object/0.36.7/object/) · [iced-x86](https://docs.rs/iced-x86/1.21.0/iced_x86/) · [gimli](https://docs.rs/gimli/0.31.1/gimli/)
- [GNU readelf](https://sourceware.org/binutils/docs/binutils/readelf.html) · [GNU objdump](https://sourceware.org/binutils/docs/binutils/objdump.html) · [LLVM objdump](https://llvm.org/docs/CommandGuide/llvm-objdump.html)
