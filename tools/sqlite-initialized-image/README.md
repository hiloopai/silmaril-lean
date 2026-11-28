# SQLite campaign client loaded-image slice

The spike connects the GCC `-O2` campaign client's read-only branch to the
retained SQLite 3.54.1 DSO through one eagerly bound ELF jump slot. It certifies
the file reads, the selected dependency resolution, and a small executable
and data mapping. The proof checks each relocated byte against the
loader model's selected slot table and the constructed memory. [Lean receipt](Replay.lean)

## Artifact identities

| SQLite binary | SHA-256 | Bytes | `sqlite3_str_length` VA |
|---|---|---:|---:|
| Campaign `libsqlite3.so.0` | `090e81e4b9943ac84089a2970fd47735e79b790501c2a3ba2ad7eb016642a729` | 1194952 | `0x25970` |
| `GccStrLengthFile.CFG.Checks` corpus `libsqlite3.so` | `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8` | 1208160 | `0x10060` |

The inputs compare different at byte 41. The 11-byte function bodies at
the respective VAs compare equal. Both binaries use the official 3.54.1
amalgamation (source ID
`555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`).
The campaign uses `THREADSAFE=1`, disables loadable extensions and database-page
mmap, and uses x86-64 generic tuning and `-pthread`. The corpus build uses
`THREADSAFE=1` with its defaults for extension loading and mmap.
[Corpus byte pin](../../Silmaril/Elf/Staged/CorpusVariants/Sqlite/N3541/Default/X8664/O2/Unstripped/Libsqlite3So/Bytes.lean)
· [Corpus CFG check](../../Silmaril/Elf/Corpus/SqliteNativeCompilers/GccStrLengthFile/CFG/Checks.lean)
· [SQLite source](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip)

The receipt uses four complete ELF files. [SHA-256 pins](pins.sha256)

| Search object | Source |
|---|---|
| Client at `0x400000` | [Independent C client](client.c) |
| SQLite DSO at `0x70000000` | Campaign build from the 3.54.1 amalgamation |
| libc at `0x71000000` | Debian amd64 `libc6` 2.41-12+deb13u4 |
| Interpreter at `0x72000000` | Same Debian package |

The chosen page-aligned bases identify a model witness. The CPU and kernel
can place objects elsewhere on an actual launch. The interpreter, libc, and
SQLite membership checks concern their on-disk metadata. Runtime search order
and those paths selecting these files are launch premises.
[Debian package](https://snapshot.debian.org/file/27904cc1b58dd79f0768ba6aa6dd993edc411b97)

## Checked boundary

- The `PT_INTERP`, `DT_NEEDED` and provider `DT_SONAME` strings come from
  the four complete inputs. For the strong, unversioned
  `sqlite3_open_v2` reference, GNU hash lookup misses in the client and
  hits in the SQLite DSO at `0xa4ca0`. The client relocation is
  `R_X86_64_JUMP_SLOT` at VA `0x4078`, with symbol 19 and addend 0.
- The client call bytes at VA `0x11bb` target its PLT entry at `0x1120`.
  That stub reads `0x4078` via RIP-relative addressing. The receipt
  checks file bytes, executable `PT_LOAD` membership, the client
  relocation footprint, and the mapped little-endian target word
  `0x700a4ca0`. It also checks five provider entry bytes in SQLite's
  executable segment and includes them in the projected witness.
- `cut_inhabited` constructs finite memory for these four ranges and gives
  the page-aligned bases and selected relocation value.
  `placed_slot_byte` proves that all eight bytes of the real slot agree
  with the model's `expectedByte` for the selected relocation, using
  `relocVal` and `Val.word` on the named scope.
  [Loader relation](../../Silmaril/Elf/Link/Dyn/Loader/Defs.lean)

A complete `ExeLoaded` witness still requires evaluation and placement of
every client slot, including its other imports, any IFUNC choices and
the modeled COPY destinations. The projected table contains one relocation.
Further obligations include loader search and mapping, relocation of the
dependency images, COPY initialization, interpreter and vDSO handoff,
CRT and constructors, and the arguments and stack/TLS state at the call.
In particular, `Elf.relas` rejects the `DT_RELR` present in both this
libc and interpreter. TLS relocations and dependency IFUNC initialization
are additional obligations. The receipt models eager binding
(`LD_BIND_NOW=1` for an analogous launch). Lazy binding starts with a
different slot value and requires a resolver transition. API execution and
the query are outside this proof.

## Replay

From the repository root with the pinned Lean toolchain:

```sh
tools/sqlite-initialized-image/check.sh /path/to/four-pinned-ELFs
```

With no argument the script downloads the official SQLite archive and the
Debian runtime package, checks their hashes, and builds the DSO and client.
This route uses Debian x86-64 GCC 14.2.0-19, binutils 2.44-3, and
`libc6-dev` 2.41-12+deb13u4. The script verifies every prepared binary
before invoking Lean. Lean checks the binary reads using
`kbytes_def … of_include`, `Rd.run_mono`, and `decide +kernel`.
It prints axiom dependencies of the public receipt theorems.
[Debian development package](https://snapshot.debian.org/file/f3859a3c0528bb85c746a18270793b295d2c80dc)
