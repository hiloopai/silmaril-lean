# Client point-query call-slot receipt

The pinned client SHA-256 is
`ee541489c3b2f351036340c4c7ca5ec59d2450dc7473dcca9a8afb6491e90d4c`.
The admitted path opens one ordinary database read-only, prepares
`SELECT amount FROM sample WHERE id=?1`, binds key 2, steps to a row, checks
and reads the integer column, steps to DONE, and finalizes and closes.
The receipt includes the same cleanup slots on error and the `sqlite3_errmsg`
diagnostic slot. SQLite entry calls made by the in-memory setup and
`--initialize` modes have their own rows below. [Client](client.c) · [ELF pins](pins.sha256)

## Complete client relocation ledger

All addresses are ELF virtual addresses and all addends are zero except the
three listed relative values. **Point** marks each of the eight success-path
slots. **Error** marks the diagnostic slot. The Lean inventory checks the
raw offset, type, dynamic symbol index and addend of every row, in file order.
The names and version annotations for the deferred rows are from GNU
`readelf -Wr --dyn-syms -V` on the pinned client.

| Table | Slot | Kind | Dynsym | Reference or addend | Boundary |
|---|---:|---|---:|---|---|
| RELA | `3db0` | RELATIVE | 0 | `+1450` | Init array |
| RELA | `3db8` | RELATIVE | 0 | `+1410` | Fini array |
| RELA | `4088` | RELATIVE | 0 | `+4088` | CRT self-pointer |
| RELA | `3fc0` | GLOB_DAT | 2 | `__libc_start_main@GLIBC_2.34` | CRT entry |
| RELA | `3fc8` | GLOB_DAT | 3 | `_ITM_deregisterTMCloneTable`, weak | Weak resolution |
| RELA | `3fd0` | GLOB_DAT | 14 | `__gmon_start__`, weak | Weak resolution |
| RELA | `3fd8` | GLOB_DAT | 20 | `_ITM_registerTMCloneTable`, weak | Weak resolution |
| RELA | `3fe0` | GLOB_DAT | 22 | `__cxa_finalize@GLIBC_2.2.5`, weak | CRT finalization |
| RELA | `40a0` | COPY | 21 | `stdout@GLIBC_2.2.5` | glibc stdio initial value |
| RELA | `40c0` | COPY | 23 | `stderr@GLIBC_2.2.5` | glibc stdio initial value |
| JMPREL | `4000` | JUMP_SLOT | 1 | `sqlite3_initialize` | Explicit initialize mode |
| JMPREL | `4008` | JUMP_SLOT | 4 | `sqlite3_exec` | In-memory setup |
| JMPREL | `4010` | JUMP_SLOT | 5 | `sqlite3_bind_int` | Point |
| JMPREL | `4018` | JUMP_SLOT | 6 | `printf@GLIBC_2.2.5` | Client result output |
| JMPREL | `4020` | JUMP_SLOT | 7 | `sqlite3_shutdown` | Explicit initialize mode |
| JMPREL | `4028` | JUMP_SLOT | 8 | `sqlite3_column_int` | Point |
| JMPREL | `4030` | JUMP_SLOT | 9 | `sqlite3_errmsg` | Error |
| JMPREL | `4038` | JUMP_SLOT | 10 | `strcmp@GLIBC_2.2.5` | Client argument dispatch and libc IFUNC |
| JMPREL | `4040` | JUMP_SLOT | 11 | `sqlite3_column_type` | Point |
| JMPREL | `4048` | JUMP_SLOT | 12 | `sqlite3_step` | Point, two call sites |
| JMPREL | `4050` | JUMP_SLOT | 13 | `fprintf@GLIBC_2.2.5` | Client error output |
| JMPREL | `4058` | JUMP_SLOT | 15 | `sqlite3_close` | Point and error cleanup |
| JMPREL | `4060` | JUMP_SLOT | 16 | `fflush@GLIBC_2.2.5` | Client output completion |
| JMPREL | `4068` | JUMP_SLOT | 17 | `sqlite3_finalize` | Point and error cleanup |
| JMPREL | `4070` | JUMP_SLOT | 18 | `sqlite3_prepare_v2` | Point |
| JMPREL | `4078` | JUMP_SLOT | 19 | `sqlite3_open_v2` | Point file open |

## What the single witness covers

| SQLite API | Client CALL VAs | Client PLT VA | DSO entry VA | DSO symbol size |
|---|---|---:|---:|---:|
| open_v2 | `11bb` | `1120` | `a4ca0` | 5 |
| prepare_v2 | `11dc` | `1110` | `ce420` | 27 |
| bind_int | `11f6` | `1050` | `49810` | 8 |
| step | `12fd`, `135f` | `10c0` | `b6600` | 3969 |
| column_type | `133e` | `10b0` | `27010` | 82 |
| column_int | `1353` | `1080` | `26ee0` | 82 |
| finalize | `128b`, `1317` | `1100` | `81280` | 223 |
| close | `121e`, `12bc` | `10e0` | `810f0` | 7 |
| errmsg | `1299` | `1090` | `4d5d0` | 298 |

Lean checks that each reference is strong and unversioned, that GNU hash
lookup misses in the client and finds the default-visible global function in
the retained DSO, and that the function's reported extent lies in its
file-backed executable `PT_LOAD`. The client CALL and PLT instruction bytes
are checked in the file, including the offsets from the next PC, and their
spans lie in the client's executable segment. This covers 12 call sites and
nine PLT stubs. Statement argument setup, execution and success/error
reachability remain separate proofs.

One memory witnesses all nine eager slot words at the bases in the
[original receipt](README.md). Each eight-byte slot belongs to the client's
file-backed writable segment, stays outside RELRO and has a unique covering
row from the **entire** 26-row inventory. The displacements fit signed
32 bits, and the loaded provider bounds fit 64 bits. The selected slots lie
within the half-open VA
interval `[0x4000, 0x4080)`. The backing is 128 bytes and there are 72
accessible bytes in nine slot regions. Lean proves that each slot loads the
resolved word and that each byte agrees with `expectedByte` for the table of
selected relocations. The code spans and their bounds are file evidence.
The memory witness covers the slot storage. [Lean receipt](Replay.lean)

## Remaining obligations

- The other 17 client rows are inventoried above. A full eager client image
  still needs their placement and initialization, including actual values of
  both COPY destinations, weak binding outcomes, the selected `strcmp`
  implementation, client I/O, and init/fini effects. Lazy binding adds the
  resolver path and the transition from the original jump-slot word.
- The scope is the pinned client, SQLite, Debian libc and interpreter in
  that order, with fixed model bases. Linux image selection, mappings,
  permissions and load bias, dependency relocations and IFUNCs, the actual
  loader/CRT and vDSO handoff, TLS/FS setup and constructors need proofs.
  Both pinned libc and loader use `DT_RELR`, which the current reader rejects
  when asked to enumerate their full relocation tables. No stock Linux
  runtime experiment accompanies this receipt. [Loader model](../../Silmaril/Elf/Link/Dyn/Loader/Defs.lean)
- The selected ABI boundary still requires SysV calls and returns, valid
  SQLite handle and statement lifetimes, initialization and mutex state,
  allocator behavior, and Unix VFS read, locking and error contracts.
  `sqlite3_open_v2` can initialize SQLite internally on the admitted path.
  The presence of an entry relocation establishes a destination and its
  bounds. Query output and error behavior need separate semantic proofs.

## DSO pin for composition

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| Existing corpus CFG pin | 1208160 | `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8` |
| Reported default unstripped x86-64 GCC 14.2.0-19 `-O2` matrix DSO | 1208160 | `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8` |
| Retained runtime DSO | 1194952 | `090e81e4b9943ac84089a2970fd47735e79b790501c2a3ba2ad7eb016642a729` |

The two repository paths reported for the matrix digest compare byte-for-byte
equal and match the corpus pin used by the CFG check. The retained DSO
differs and has extension loading and database-page mmap disabled.
The equal 11-byte `sqlite3_str_length` bodies are one local observation
at different VAs. Composition needs the exact artifact and its own placement,
relocations and boundary conditions. [Native compiler endpoint](../../corpus/sqlite/equivalence/native-compilers/manifest.json)
· [Matrix](../../corpus/matrix.json) · [Corpus variant receipt](../../corpus/variants/sqlite/3.54.1/default/x86_64/O2/unstripped/receipt.json)

Use the retained `090e81e4…` DSO as the eventual client composition pin
to preserve the campaign profile already replayed here. Keep the published
corpus and matrix artifacts as reference builds. Migrate in small steps:

1. Promote the reproducible campaign build as a named corpus variant with
   its own build flags, hash, ELF metadata, and function map.
2. Re-index one leaf such as `sqlite3_str_length` and check its exact span,
   placement, relocations and ABI prerequisites under the retained DSO.
   Regenerate leaf certificates for the chosen API path as each becomes needed.
3. Join the rechecked leaf contracts to this call-slot table. Use one
   shared artifact identity and bases at each join. Extend the projected
   image only as required by those proofs, recording glibc, CRT, allocator
   and VFS assumptions separately.

## Replay

From the repository root with the pinned Lean toolchain:

```sh
tools/sqlite-initialized-image/check.sh /path/to/four-pinned-ELFs
```

Omit the directory to rebuild the client and DSO from the pinned sources and
fetch the matching Debian loader and libc. The script compares all four
digests before Lean runs. [Build requirements](README.md#replay)
