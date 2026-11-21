# SQLite 3.54.1: one checked effect boundary

`sqlite3_mutex_leave` is the first slice, not a SQLite VM implementation. The
[VM contract](../../Silmaril/Machine/SqliteMutex/Thms.lean) says that null
returns silently, and that a live mutex owned by the caller generates exactly
one typed `leave` request for that handle. The [ELF proof](../../Silmaril/Elf/Corpus/SqliteMutex/Thms.lean)
transfers that contract to a three-instruction cut of the pinned library's
`X86.Ext.Wire.step` execution. The nonnull cut ends **at the target of the
indirect jump**, before the first handler instruction. It observes neither a
pthread unlock nor the handler's return; an `xMutexLeave` reply would be `Unit`.

## Source and interface audit

Line numbers refer to the [pinned `sqlite3.c`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c),
not a floating upstream main. Public docs: [release](https://sqlite.org/releaselog/3_54_1.html),
[amalgamation](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip),
[threading modes](https://sqlite.org/threadsafe.html), and the AMD64 psABI
[calling sequence](https://gitlab.com/x86-psABIs/x86-64-ABI).

| Interface | Pinned implementation and first useful laws |
| --- | --- |
| [VFS](https://sqlite.org/c3ref/vfs.html) / [file methods](https://sqlite.org/c3ref/io_methods.html) | `sqlite3_file` at 1068 begins with `pMethods`; `sqlite3_io_methods` at 1175 and `sqlite3_vfs` at 1834 are **separate** versioned tables. `sqlite3OsOpen` (27880) calls `xOpen` with VFS, filename, caller-supplied file storage of at least `szOsFile`, flags and optional output flags. A nonnull `pMethods` makes `xClose` necessary even after failed open; `sqlite3OsClose` (27747) clears it. `sqlite3OsRead` / `sqlite3OsWrite` (27753/27757) pass the live file, buffer, `int` amount and `i64` offset and preserve the integer status. For a read handler, specify owned writable bytes, signed range guards, frame outside the buffer, and return code; a short read is `SQLITE_IOERR_SHORT_READ` with a zero-filled unread suffix, not UB. File locks are VFS effects, not SQLite thread mutexes. Version 2 adds shared-memory methods (`xShm*`), version 3 adds `xFetch`/`xUnfetch`; no WAL/shared memory, mapping, file control, Unix VFS or POSIX fidelity is checked here. |
| [Allocator](https://sqlite.org/c3ref/mem_methods.html) | `sqlite3_mem_methods` (2135) provides `xMalloc(int)`, `xFree(void*)`, `xRealloc(void*,int)`, `xSize`, `xRoundup`, `xInit`/`xShutdown` with `pAppData`; `sqlite3_config` copies the table (188861). `sqlite3Malloc` (32122) rejects zero/oversize, uses `mem0.mutex` and `mallocWithAlarm` (32072) with memory status active, otherwise calls `xMalloc` directly. `sqlite3_free` (32217) has its own null/status path. Model live disjoint aligned blocks, null as modeled failure, `realloc` failure preserving the old allocation, and free consuming ownership; `xSize`/`xRoundup` coherence and concurrent use depend on the configured serialization (`SQLITE_DEFAULT_MEMSTATUS=1`, at 15287; can be disabled). No heap hook, lookaside or allocation accounting is modeled here. |
| [Mutex API](https://sqlite.org/c3ref/mutex_alloc.html) / [method table](https://sqlite.org/c3ref/mutex_methods.html) | The public API (8816–8832) allows null as a no-op and requires the live mutex to be entered by the same thread before `leave`. Methods need not accept null. `sqlite3_mutex_enter` (30692) and `sqlite3_mutex_leave` (30718) use `sqlite3GlobalConfig.mutex`; `xMutexEnter` and `xMutexLeave` (8900) take a single opaque `sqlite3_mutex*` and return `void`; `xMutexTry` returns a status. The default Unix table is pthread-backed (`pthreadMutexEnter`/`pthreadMutexLeave`, 31244/31343). `sqlite3MutexInit` (30598) installs the default or configured methods, and `SQLITE_CONFIG_MUTEX` copies an override before initialization (188848). A future linked handler must describe the owner and recursion-depth update and frame unrelated locks; a recursive leave need not unlock the underlying mutex yet. No `enter`, try, scheduling, or ownership-transition proof is included. |
| Lifetime (not a universal retain/release interface) | `PgHdr.nRef` (18392–18415) and `PCache.nRefSum` (56098) are SQLite state. `sqlite3PcacheFetchFinish` (56585) and `sqlite3PcacheRef` (56624) increment them; `sqlite3PcacheRelease` (56608) decrements them, unpinning a clean page only at zero. Only an actual custom [page-cache API](https://sqlite.org/c3ref/pcache_methods2.html) (`sqlite3_pcache_methods2`, 9911) exposes `xFetch`/`xUnpin` across a method boundary; it does not expose those increments. Connections use `connectionIsBusy`, `sqlite3Close` and `sqlite3LeaveMutexAndCloseZombie` (189624, 189638, 189747) to defer destruction with outstanding statements/backups, rather than handing out a generic connection reference count. `BtShared.nRef` (72108, `removeFromSharingList` at 75590) and `unixShm` references (45220, `unixShmPurge` at 45465) are internal too. No refcount effect is added. |

The corpus's default ELF uses GCC Debian 14.2.0-19, GNU ld 2.44, `-O2 -g0
-ffile-prefix-map=/build/sqlite=. -DSQLITE_THREADSAFE=1 -MMD -fPIC` for the
library and `-shared -Wl,-soname,libsqlite3.so.0 -lm` for its link. No extra
SQLite defines: `SQLITE_DEBUG` is absent so the amalgamation defines `NDEBUG`
(15343–15357); the callback assertion does not compile in. Runtime reports
`THREADSAFE=1`, `MUTEX_PTHREADS`, `SYSTEM_MALLOC`. `SQLITE_THREADSAFE=1` defaults
to serialized, `2` defaults to multithread, and builds with mutex support may
change mode at startup (188821–188845), with per-connection flags where
applicable. `0` (`SQLITE_MUTEX_OMIT`, 18602–18633) compiles internal mutex calls
away; the corpus `small` profile also omits extension loading and disables
default memory status. Win32/no-op tables, debug, `small`, FTS5/RTree profiles
and other architectures are unaudited by the proof.

## Binary, trust and cut

- Archive SHA-256 `0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`;
  SHA3-256 `92281c86e2957f9b9305890f9ac04204caa7b677cc868dc326d942689df28e30`.
  The downloaded archive's `sqlite3.c`, `sqlite3.h`, `shell.c` match the
  tracked files byte-for-byte; [source manifest](../../corpus/sqlite/upstream.sha256).
  Source ID is `2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
- The original source rebuilt byte-for-byte on x86-64 Debian using the
  [receipt](../../corpus/elf/sqlite/x86_64/receipt.json) commands. ELF library
  SHA-256 `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8`;
  shell `26c71865aa7f7ce686f47e8b3c306b98b3d7fb3b181a759f388bb01284c1b870`.
  The [function map](../../corpus/sqlite/funcmap/x86_64/libsqlite3.so.json)
  supplies the source locator (decl 30718); Lean reuses the generated
  `Libsqlite3So` parse, `.dynsym` entry 77 and kernel-byte mapping, not DWARF
  or `objdump` as proof oracles. `symbol_identity` checks name/type/extent;
  `code_at` checks the executable `PT_LOAD` (file offset and VA `0xf000`).

```text
ff70  48 85 ff           test rdi,rdi
ff73  74 0b              je ff80
ff75  ff 25 d5 f6 0f 00  jmp qword ptr [rip+0xff6d5]  ; ff7b + ff6d5 = 10f650
ff7b  0f 1f 44 00 00     nop (not executed)
ff80  c3                 ret
```

- **Initial/image hypotheses:** fixed link-time VAs (not a proof of Linux
  loading, relocation or ASLR), entry at `0xff70`, `Region.LoadedIn` over all
  17 bytes, readable stack return slot, and a readable nonzero callback at
  `0x10f650` on the nonnull path. `nm` places `sqlite3Config` at `0x10f5c0`;
  the slot is `+0x90`, also checked with GCC `offsetof` on the amalgamation.
  Passing through `RDI` and keeping `RSP` and all GPRs
  unchanged on the tail jump passes the incoming System V call state along.
  The null path advances RSP by eight and returns to the designated address.
  Callee-entry alignment, canonical addresses/lifetimes, no competing slot
  update, executable target, correct installed C signature and a handler
  realization are linking/ABI obligations, not inferred from the slot value.
- **Explicit no-UB obligation:** `Safe ((contract env).spec mutex)` discharges
  at null or by live/same-thread-owned/installed facts in the context. The
  checked caller contract terminates at a boundary and excludes extra effects,
  faults, divergence and UB for admitted runs. The closed behaviour set of
  an unowned live mutex is top, via `Observable.close`; that is permission
  for any behavior, not a promise of SIGILL (or any other concrete signal).
  The machine may still jump successfully for those same pointer bits.
  No native UB call is executed. No callback status is returned by this
  `void` wrapper; VFS and allocator modeled errors belong to other handlers.
- **Named lower semantics:** byte-faithful `Wire.decode` handles the indirect
  jump (plain `Ext.decode` does not), `Wire.step_of_fetch` connects consumed
  spans from `Region.LoadedIn` to actual `Wire.step`. The executable cut
  recognizes a retired step at `0xff75` and a `RET` to the designated caller;
  those classifications are justified *under* the checked code/image premise.
  The proof does not start from two matching success assumptions: it produces
  the exact third-step outcome in both paths and checks the projected `RDI`
  event. Undefined flags in x86, fetch/data faults, trap, undecodable bytes
  and budget rejection are not C UB. The finite cut's budget rejection is
  neither a process exit nor a proof of divergence.

## Replay

From the repository root (use the pinned Lean toolchain):

```sh
lake build --wfail Silmaril.Elf.Corpus.SqliteMutex.Checks
make check CHECK_TARGETS=Silmaril.Elf.Corpus.SqliteMutex.Checks
(cd corpus/sqlite && sha256sum -c upstream.sha256)
(cd corpus/elf/sqlite/x86_64 && sha256sum -c SHA256SUMS)
objdump -d --disassemble=sqlite3_mutex_leave corpus/elf/sqlite/x86_64/libsqlite3.so
readelf -Wls corpus/elf/sqlite/x86_64/libsqlite3.so
printf '%s\n' '#include "sqlite3.c"' \
  '_Static_assert(sizeof(void *) == 8, "pointer width");' \
  '_Static_assert(offsetof(struct Sqlite3Config, mutex.xMutexLeave) == 0x90, "slot");' | \
  gcc -I corpus/sqlite/upstream/sqlite-amalgamation-3540100 -DSQLITE_THREADSAFE=1 -x c -fsyntax-only -
```

For a rebuild, download the archive above, verify its hash before unpacking
under `/build/sqlite`, compare its source files to the tracked sources, then
run the receipt's four commands in the extracted directory with
`SOURCE_DATE_EPOCH=1762128000 LC_ALL=C TZ=UTC` and `umask 022`. Compare with
`cmp` or `SHA256SUMS`. See the [corpus build guide](../../corpus/README.md) if
the host compiler/linker differ. For the native comparison, the probe installs
a counting adapter around the *real* default leave handler, checks the null
call and a live owned mutex, and links the actual pinned bytes, not a shim of
`sqlite3_mutex_leave`:

```sh
scratch=$(mktemp -d)
pinned="$PWD/corpus/elf/sqlite/x86_64/libsqlite3.so"
ln -s "$pinned" "$scratch/libsqlite3.so.0"
gcc -Wall -Wextra -Werror -I corpus/sqlite/upstream/sqlite-amalgamation-3540100 \
  scripts/sqlite-mutex/probe.c "$pinned" -o "$scratch/probe"
LD_LIBRARY_PATH="$scratch" "$scratch/probe"
LD_LIBRARY_PATH="$scratch" corpus/elf/sqlite/x86_64/sqlite3 :memory: \
  'select sqlite_version(),sqlite_source_id(); pragma compile_options;'
```

The Lean fixtures use actual function bytes with modeled stack and slot
contents: the owned case proves `Entry` and `Safe` together, and checks the
observation. Additional executable checks exercise null without a slot,
nonnull without a slot (data fault), and insufficient budget (validation
failure). The unowned case proves UB closure in the kernel. No new axiom or
compiler-evaluated proof is used. Native comparison/rebuild is separate
evidence, not formal C→x86, System V ABI, or hardware validation.

## Repeat for the next slice

1. Record archive hash, upstream version/config, source span, prototypes and
   reviewed preconditions. Ask an AI to propose a **source-only** candidate
   with typed requests/replies and independent handler laws. Preserve its
   provenance separately from the source; no generated spec is an axiom.
2. Independently select a pinned symbol, build receipt, ELF mapping, and
   load/ABI/exit boundary; check the literal bytes in the kernel. Generate
   decoder/listing hypotheses if useful, but prove fetch and operational steps
   against the existing model. Never derive both reference and target from
   the same lift. External observations go with the evidence, not the proof.
3. Prove a no-UB obligation and total cut correspondence; check at least one
   admitted and one excluded input. Report unsupported paths/byte subsets,
   assumptions, proof axioms, and native comparisons separately. Keep model
   faults and modeled service errors distinct from source UB.

Suggested sequence: (1) use the same pattern for a VFS-file `xRead` call site
with output frame and `SHORT_READ` law; (2) add the memstatus-disabled
allocator dispatch and allocation-result/ownership laws before composing
with `mem0.mutex`; (3) add mutex enter/leave linking to a sequential handler
contract, then a separate concurrency/ownership refinement. Shared follow-up
touchpoints are [#1090](https://github.com/hiloopai/silmaril-lean/pull/1090) for
first exits, [#1110](https://github.com/hiloopai/silmaril-lean/pull/1110) for
instruction reads/image backing, [#1118](https://github.com/hiloopai/silmaril-lean/pull/1118)
for typed process requests, and [#1115](https://github.com/hiloopai/silmaril-lean/pull/1115)
for decoder graphs. This slice adds no generic exit, syscall, image, UB or
decoder API and does not depend on those changes.
