# SQLite VFS-file read: one inlined dispatch

This pilot checks the three instructions that dispatch `xRead` on the
non-WAL branch of SQLite's `readDbPage` (the branch with no WAL frame to
read, not a build without WAL). It stops at the installed handler's entry,
before fetching any handler instruction. It does not use a shim, modified
source, or an alternate SQLite build.

## Source and binary provenance

The corpus pins the original [SQLite 3.54.1 amalgamation](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip)
in [`corpus/sqlite/package.toml`](../../corpus/sqlite/package.toml).
The archive SHA-256 is `0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`.
The x86-64 `libsqlite3.so` SHA-256 is `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8`.
The sources match the archive byte-for-byte. A rebuild in
`/build/sqlite/sqlite-amalgamation-3540100` with Debian GCC 14.2.0-19 and
GNU ld 2.44 matched the corpus ELF byte-for-byte. The library command is:

```sh
gcc -O2 -g0 -ffile-prefix-map=/build/sqlite=. -DSQLITE_THREADSAFE=1 -MMD -fPIC \
  -c sqlite3.c -o sqlite3.o
gcc -shared -Wl,-soname,libsqlite3.so.0 -o libsqlite3.so sqlite3.o -lm
```

In the pinned [`sqlite3.c`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L27753),
`sqlite3OsRead` calls `id->pMethods->xRead(id,pBuf,amt,offset)`. The
[`readDbPage` call](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L62034)
uses `(pgno - 1) * pageSize` for the offset. The ELF has **no separate
`sqlite3OsRead` symbol or named clone**; just checking its exported symbols
would not establish that. Its full symbol table identifies `readDbPage`
as local `STT_FUNC` #941, at `0x4b020` with size 315. The listing shows
the inlined method-table dispatch at ELF virtual and file addresses
`[0x4b10d, 0x4b117)`:

```text
4b10d  48 8b 07     mov  (%rdi),%rax
4b110  48 0f af ca  imul %rdx,%rcx
4b114  ff 50 10     call *0x10(%rax)
```

`0x4b117` is the pushed continuation; its comparison with `522` and the
pager's conversion of `SQLITE_IOERR_SHORT_READ` to `SQLITE_OK` are outside
the cut. So are the preceding pager loads, the other indirect call in
`readDbPage`, and the other `sqlite3OsRead` call sites. As separate ELF
inspection evidence, `posixIoMethods` is at `0x10e220`, with
`R_X86_64_RELATIVE` at its `xRead` slot `0x10e230` and addend `0x159b0`
(`unixRead`). This is not a loader or VFS installation theorem.

```sh
elf=corpus/elf/sqlite/x86_64/libsqlite3.so
sha256sum "$elf"
nm -an "$elf" | rg 'sqlite3OsRead|readDbPage|posixIoMethods|unixRead'
readelf -Ws "$elf" | rg 'sqlite3OsRead|readDbPage|posixIoMethods|unixRead'
readelf -lW "$elf"
readelf -rW "$elf" | rg '10e230'
objdump -d --disassemble=readDbPage "$elf"
```

## VM contract and what is checked

- **Interface.** The [VFS](https://sqlite.org/c3ref/vfs.html) opens a
  [`sqlite3_file`](https://sqlite.org/c3ref/file.html); reads go through
  its [`sqlite3_io_methods`](https://sqlite.org/c3ref/io_methods.html)
  table, not through a method on the VFS object. In the pinned header
  embedded in `sqlite3.c`, `pMethods` is at source line 1069 and the
  version-1 `int (*xRead)(sqlite3_file*, void*, int, sqlite3_int64)` is at
  line 1178. On this SysV x86-64 profile, the byte offsets are 0 and 16.
- **Admission.** The file and installed read method are live and stable
  during the call. The context supplies exclusive writable access to the
  output span; being mapped writable alone does not confer that ownership.
  The pilot admits a positive signed 32-bit count, a nonnegative signed
  64-bit offset, a signed-representable `offset + count`, and a nonwrapping
  buffer span. These are conservative pilot preconditions, not a claim
  that every VFS accepts exactly these inputs. The pinned `unixRead`
  asserts positive count and nonnegative offset (lines 44166–44176).
- **Handler.** The docs require zero-fill for `SQLITE_IOERR_SHORT_READ`
  (pinned lines 1168–1172; `unixRead` at 44229–44231). The independent
  `Handler` law adds a stable finite file snapshot: success supplies all
  requested bytes; a short read supplies the available prefix and zeroes
  the entire unread suffix. Other status bits round-trip losslessly;
  the buffer contents within the span are unspecified on other errors.
  The frame is on the caller-visible buffer view, not on handler-private
  state such as `lastErrno`. `short_read` proves the suffix and frame from
  this law, not from the ELF. No lock transitions or POSIX I/O are modeled.
- **Dispatch.** `symbol_identity` uses the corpus `.symtab` row;
  `code_at` uses its executable `PT_LOAD` and kernel bytes. `run_dispatch`
  fetches and decodes using `X86.Ext.Wire.step` and proves that under
  `Entry` the cut terminates in exactly three steps. At the cut start
  RDI/RSI are file/buffer, RDX is the positive count zero-extended, and
  RCX is the zero-extended page index from the instructions before the cut.
  The proof establishes the exact nonwrapping offset, the outgoing request
  in SysV registers, the callback RIP, the decremented RSP and pushed
  continuation. The only memory write is the eight-byte stack slot;
  disjointness gives `buffer_unchanged`. The proof assumes the bytes
  loaded at the stated addresses, readable file/table entries, a nonzero
  target, and an aligned pre-call stack with a readable/writable return
  slot. It does not derive a real process mapping, prove an executable
  callback target, or validate C→assembly.
- **Observations.** `sound` additionally requires `Safe` for the VM
  request. It transfers the singleton dispatch trace ending at
  `handlerEntry`, not a handler return status. An input excluded by
  admission has a UB marker whose observation closure is top, not a
  particular signal. Faults in the lower semantics, unsupported decode,
  and cut validation/budget failure are separately classified. The runner
  is only certified under `Entry`, not a validator for arbitrary code.

The kernel checks an admitted page-3 read of 512 bytes at offset 1024 with
the attested code bytes and modeled memory (including the POSIX table slot
at zero load bias). This is not a native end-to-end SQLite run. Regressions
also cover an absent slot (data fault), insufficient budget (validation
failure), a negative offset (UB top), and a short read with one data byte,
two zero bytes, and the outside frame. The ELF, operational semantics and
source-side candidate are separate: generated specs/listings are hypotheses,
not axioms. Reuse the workflow by recording the source/API and candidate law,
independently pinning and locating bytes, then checking the cut and fixtures.

```sh
lake build --wfail Silmaril.Elf.Corpus.SqliteRead.Checks
make check CHECK_TARGETS=Silmaril.Elf.Corpus.SqliteRead.Checks
```

## What composition with mutex release needs

1. Link a concrete `xRead` target: prove that loading/relocating the chosen
   ELF and opening a file establishes the correct typed, executable slot
   and live file/buffer/stack state. Prove or explicitly assume a handler
   contract over the resulting entry: execution returns to `0x4b117`,
   restores RSP and callee-saved state, projects EAX via `Status.ofCode`,
   and satisfies `Handler` on the visible memory view. Prove the file and
   shared-state frame needed beyond that view, and the no-UB obligation
   on the covered handler executions. The pager continuation needs its
   own check before claiming short-read normalization.
2. For a named path to `sqlite3_mutex_leave`, prove the intervening code
   and read-handler effects preserve or re-establish the same thread's
   mutex ownership/lifetime, installed method and release ABI premises.
   Only then can the observations be sequenced into read then leave.
   Actual unlock additionally needs a linked leave-handler return and
   owner/depth transition; a dispatch is not itself an unlock. No such
   call chain or concurrent safety result is inferred from the pilots.
