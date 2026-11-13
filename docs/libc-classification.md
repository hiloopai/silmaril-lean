# Classifying C library specifications

A scheme for describing what a set of C library specifications covers: which functions exist,
where each is standardised, what it does, how strong our spec of it is and whether that spec is
proved, per build of the library. It is meant for a problem catalogue that states contracts of
real `libc.so` files (glibc, musl) against their bytes, and for measuring how much of POSIX such a
catalogue covers. The scheme is independent of any one catalogue; the tables it describes are
data, kept beside the catalogue, and generated from named sources.

## Keys

* A **name** is a C-level function name (`printf`, `stat64`, `__printf_chk`). Origin and kind are
  properties of names.
* A **symbol id** is an exported dynamic symbol of one library file: `name@version` for glibc
  (`memcpy@GLIBC_2.14`, `memcpy@GLIBC_2.2.5`), the bare name for musl. Spec strength and proof
  status are properties of symbol ids, per **pin** (one library file, identified by its sha256).

The classification is a separate table keyed by name (and a per-pin table keyed by symbol id),
not columns of the problem records: a problem record says what is stated; the classification says
what the stated thing is.

## Axis 1: origin

| origin | meaning | how it is assigned |
|---|---|---|
| `isoc` | ISO C (C99; C11 for the C11 additions), as POSIX aligns with it | the POSIX page says it is aligned with ISO C, the name is declared in an ISO C header, and the declaration carries no option code other than `OB` |
| `posix` | POSIX.1 base, including the `CX` extensions of ISO C | in the POSIX index, no option code |
| `xsi` | the X/Open System Interfaces option | margin code `XSI` |
| `posix-opt` | another POSIX option: `ADV`, `TPS`, `MSG`, `SPN`, `TRC`, `TSA`, ... | any other margin code (`OH` and the `MX*` math codes are not options) |
| `lfs` | a large-file `*64` variant of a standard name (`stat64`, `fopen64`) | the name minus `64` is a standard name (not the `_Float64` functions) |
| `ext` | a GNU, BSD or System V extension, or no standard | man-pages STANDARDS says GNU, BSD, SVr4, None, or nothing is known |
| `linux` | a Linux-specific interface (`epoll_create`, `memfd_create`) | man-pages STANDARDS says Linux |
| `abi` | an ABI entry point of the implementation: fortify (`__*_chk`), standard-mode aliases (`__isoc99_scanf`, `__isoc23_strtol`, `__xpg_basename`), libio and loader plumbing (`_IO_*`, `_dl_*`), `GLIBC_PRIVATE`, and every non-default (compat) version of a symbol | a leading `_` for names; the version for symbols |

Precedence: the POSIX inventory first, then the `abi` and `lfs` rules, then man-pages. The edition
(`POSIX.1-2017`, `POSIX.1-2024`, `C99`, `C11`, `GNU`, ...) is recorded beside the origin.

**Obsolescence is a flag, not an origin**: `ob` (POSIX margin code `OB`), `removed2024` (in
POSIX.1-2017, not in 2024), `compat` (a non-default symbol version), `private` (`GLIBC_PRIVATE`).
`gets` is `isoc` with `ob,removed2024`.

### Origins and the lattice

A catalogue organised as a lattice of specifications (POSIX, the GNU convention, the portable
meet, glibc and musl as nodes) relates to origins through **the lowest node that has a function of
the origin**: `isoc`, `posix`, `xsi`, `posix-opt` → the POSIX node; `lfs`, `ext`, `linux`, `abi` →
the GNU-convention node (which, by design, includes the fortify entry points). A catalogue entry
**agrees** with its tag when an entry with a POSIX contract is a POSIX name first in the edition
the entry gives, and an entry without one sits at or above its origin's node, or at the GNU node,
which may hold the GNU version of a POSIX name (`basename`, `strerror_r`). This is checkable by
evaluation and catches an entry dated to the wrong edition (`aligned_alloc` is C11 but entered POSIX
only in 2024).

## Axis 2: kind

What the function does, for choosing a model and a spec style.

| kind | examples | the state a spec needs |
|---|---|---|
| `pure` | `strlen`, `memcpy`, `qsort`, `strtol`, `snprintf`, `sigemptyset` | memory (plus `errno`, a PRNG state) |
| `stream` | `printf`, `puts`, `getchar`, `scanf`, `perror` | the standard streams' bytes |
| `file` | `fopen`, `fprintf`, `fread`, `fflush`, `getline`, `opendir` | `FILE *`/`DIR *` objects, buffers, the file system |
| `syscall` | `read`, `write`, `open`, `mmap`, `stat`, `socket` | the kernel: one or a few syscalls |
| `process` | `exit`, `fork`, `execve`, `sigaction`, `setjmp`, `getenv`, `dlopen` | the process: handlers, environment, image |
| `locale` | `isalpha`, `setlocale`, `mbrtowc`, `iconv`, `strftime`, `localtime` | the locale, conversion state, time zone |
| `thread` | `pthread_*`, `sem_*`, `thrd_*`, `mtx_*` | threads, futexes |
| `alloc` | `malloc`, `free`, `calloc`, `realloc`, `strdup` | the heap |
| `math` | `sin`, `frexp`, `abs`, `div` | floating point (mostly in `libm`) |
| `net` | `getaddrinfo`, `inet_pton`, the Sun RPC functions | resolver configuration, the network |
| `sysdb` | `getpwnam`, `getgrent`, `getutxent` | the system databases (NSS) |
| `internal` | libio and loader plumbing | — |

Kinds are assigned by ordered rules, each recorded with the row (`ksrc`): explicit name sets
(the allocator, the standard-stream functions, the `s*printf` family as `pure`), name patterns,
the POSIX header (`<stdio.h>` → `file` unless another rule fired; `<pthread.h>` → `thread`;
`<unistd.h>`, `<fcntl.h>`, `<sys/*.h>` → `syscall`), the prototype (`FILE *`), then the
implementation's own call-graph kind where one is available. An `abi` name takes the kind of the
name it stands for (`__fprintf_chk` is `file`). A syscall wrapper also records the Linux syscall it
issues (`open` → `openat`, `stat` → `newfstatat`) and whether a kernel-side spec of that syscall
exists, so its contract can be stated against it.

## Axis 3: spec strength (per symbol id)

| strength | meaning |
|---|---|
| `none` | no row |
| `export` | an export-binding row: the file exports the symbol at an address, a function or an IFUNC |
| `posix_safe` | the generic row: the code returns per System V, keeps a hidden invariant and touches nothing else; says nothing about the result |
| `doc` | a prose contract (a documented plan), no Lean statement |
| `narrow` | a Lean contract for one use (a format such as `"%d\n"`, a happy path, a stream subset), **trusted** by the proofs that use it, not proved of the library |
| `functional` | a general contract of the function at a lattice node: a pure row (one per IFUNC variant) or a member of a family row (allocator, ctype, conversions, stdio) |

The order is the list order. A function has a **real** spec when its strength is `narrow` or
`functional`; `export`, `posix_safe` and `doc` are generic. A C name counts at the best of its own
symbols and of the ABI entry points it compiles to (`scanf` → `__isoc99_scanf`, `printf` →
`__printf_chk` under `_FORTIFY_SOURCE`).

## Axis 4: proof status (per symbol id and pin)

Separate from strength: `proved` (every row of the strength is a theorem), `open`,
`export-proved` (the export row is a theorem, the stronger rows are open), `trusted` (a narrow
contract), `prose`. Proofs of the same function elsewhere (a variant proved under another
statement, not yet ported) are listed with the source, so a row is never counted as proved on the
strength of a different statement.

## Tables

| table | key | columns |
|---|---|---|
| POSIX inventory | name | `in2017`, `in2024`, margin codes, header, ISO C alignment; with its source URLs and fetch date |
| names | name | origin, edition, codes, flags, kind, header, location in the reference build (`libc`, `libm`, `object`, `absent`), the rules that set origin and kind |
| per pin | symbol id | name, version, default, origin (or `abi` for compat/private), kind, strength, status, flags, syscall, sources of the strength |
| side tables | name | contracts outside the catalogue (`narrow`, `doc`) with where they are stated; proofs outside the catalogue |

The generator reads only named sources: the POSIX index (The Open Group, `idx/functions.html` and
each `functions/<name>.html`, for POSIX.1-2017 and POSIX.1-2024), the Linux man-pages STANDARDS
sections, each pin's dynamic symbol table, and the catalogue's own rows and verdicts. A wrong tag
is corrected by a rule in the generator, not by editing a generated table.

## Measuring POSIX completeness

Coverage is reported for a pin against the POSIX inventory, in buckets: real spec, `doc` only,
`posix_safe` only, `export` only, no row, and **not in the library file** (a `libm` function, an
object such as `environ`, a macro such as `FD_SET`, a `libc_nonshared.a` stub such as `atexit`, or
not provided at all, such as the XSI STREAMS and the tracing option). Counts are broken down by
kind and by origin, and the stream, file and syscall-wrapper functions without a real spec are
listed by name: they are the next batches.

## Caveats

* Kinds and the origins of names outside POSIX are heuristics; the rule that fired is recorded.
* POSIX's math functions live in `libm.so.6` for glibc and in `libc.so` for musl; a catalogue that
  pins only `libc.so.6` counts them as not in the file.
* `isoc` follows POSIX's alignment (C99 for 2017, C17 for 2024), not the C standard's own index.
