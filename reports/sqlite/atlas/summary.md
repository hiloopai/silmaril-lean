# SQLite 3.54.1 source and dependency atlas

The selected library translation unit contains **2,615 SQLite function definitions** and **13,749 AST call sites**. Clang tied 12,766 sites to SQLite bodies. 254 sites are indirect with unresolved targets.

Source ID `2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`. The generator verifies the published SHA3-256 digests for the release amalgamation, full source tree and pre-amalgamation staging bundle. [SQLite downloads](https://sqlite.org/download.html) · [Release notes](https://sqlite.org/releaselog/3_54_1.html) · [Architecture](https://sqlite.org/arch.html)

## Measured profile

Native `x86_64-linux-gnu`, glibc 2.41. Shared flags `-std=gnu11 -O2 -fPIC -pthread -DSQLITE_THREADSAFE=1 -DSQLITE_OMIT_LOAD_EXTENSION=1 -DSQLITE_MAX_MMAP_SIZE=0`. Both preprocessors reported `NDEBUG=1`, `SQLITE_OS_UNIX=1` and the requested threading, extension and mmap settings. The GCC object passed the file-backed SQL smoke test and defined neither load-extension API entry point.

- GCC build and preprocessing with gcc (Debian 14.2.0-19) 14.2.0.
- AST and record layouts with Debian clang version 19.1.7 (3+b1).
- Clang driver preprocessing with Debian clang version 19.1.7 (3+b1).
- Clang processed the original C with its own preprocessor. GCC and Clang preprocess independently. For example, the preprocessed `sqlite3Get4byte` body selects `byte_subscripts` with Clang and `memcpy_and_bswap` with GCC. The inventory describes the Clang source view. Correspondence to GCC binaries or the repository build matrix remains unverified.

## Definition and call denominators

- SQLite inventory is one row per function-definition cursor in release `sqlite3.c`. It has 2,341 internal and 274 external linkage definitions, and 274 definitions declared in the embedded public header family.
- The same parse yielded 26 out-of-unit definitions, 0 locationless definitions and 3,724 located non-definition declaration cursors across the whole translation unit. These are excluded from the SQLite body denominator.
- SQLite definitions outside embedded markers total 1. The generated trailer is mapped explicitly. Unmapped definitions total 0. Definitions without a physical body range total 0. Plain names shared by multiple definitions total 0.
- Every `CallExpr` visited in those SQLite bodies contributes one site. The direct SQLite sites form 8,911 distinct ordered caller/callee pairs including self edges. Sites without a physical location total 0. Callers may appear in several rows below.

| Call classification | Sites | Caller definitions |
| --- | ---: | ---: |
| `sqlite_definition` | 12,766 | 2,052 |
| `system_definition` | 0 | 0 |
| `external_declaration` | 685 | 393 |
| `compiler_intrinsic` | 44 | 23 |
| `sqlite_declaration_only` | 0 | 0 |
| `locationless_declaration` | 0 | 0 |
| `definition_unmatched` | 0 | 0 |
| `indirect` | 254 | 190 |

## Architectural regions

| Region | Definitions |
| --- | ---: |
| Allocator | 53 |
| B-tree | 214 |
| Concurrency | 27 |
| Connection and public API | 194 |
| Name resolution and expressions | 211 |
| Page cache | 66 |
| Pager and journal | 199 |
| Parser | 25 |
| Planner and SQL code generation | 665 |
| SQL builtins | 213 |
| Tokenizer | 15 |
| Utilities and portability | 150 |
| VFS | 151 |
| Virtual machine | 393 |
| Virtual tables and extensions | 39 |

Architecture confidence is high for 2,615 definitions with an explicit section-to-region mapping and low for the remaining 0. This estimates placement from source-file responsibility. Mixed-role functions can warrant a different assignment.

There are 72 source namespaces. `generated_section` 33, `unique_basename` 2,582.

Definitions carry a release, physical file, line, column and spelling in their IDs. Nested markers identify embedded headers. Unique canonical basenames are origin candidates. Generated sections keep their generated label and list the input grammar, templates or generator scripts where identified. Source-line offsets remain physical amalgamation coordinates. The shell, inactive conditional code and separately built extensions fall outside the translation unit.

Largest cross-region dependencies by direct call-site count.

| Caller region | Callee region | Sites |
| --- | --- | ---: |
| Planner and SQL code generation | Virtual machine | 1,675 |
| Planner and SQL code generation | Name resolution and expressions | 839 |
| Planner and SQL code generation | Utilities and portability | 521 |
| SQL builtins | Virtual machine | 393 |
| Planner and SQL code generation | Allocator | 280 |
| Name resolution and expressions | Virtual machine | 238 |
| Virtual machine | Utilities and portability | 173 |
| Parser | Planner and SQL code generation | 154 |

## C features, layouts and effects

2,594 definitions have declaration or macro evidence from an embedded or system header. 288 referenced record layouts include 3 with unavailable size. Sizes, alignment and field bit offsets are Clang values for this target. Layout references describe syntactic type usage. Included declarations, pointer parameter shapes and pointee qualifiers help identify cases for ownership review.

Local tags describe evidence such as byte buffers, members, nonlocal storage and calls at allocator, VFS or locking boundaries. Reachable tags are a union over the resolved SQLite call graph. The unknown tag remains on open direct or indirect boundaries and can propagate. These tags provide source-review candidates. Observable purity, memory ownership, bounds, aliasing and synchronization properties require separate verification.

| Tag | Local functions | Reachable via SQLite edges | Via callees only |
| --- | ---: | ---: | ---: |
| `allocator` | 409 | 1,547 | 1,141 |
| `buffer` | 1,297 | 1,664 | 606 |
| `callback` | 417 | 1,775 | 1,457 |
| `globals` | 349 | 1,810 | 1,574 |
| `locks` | 198 | 1,644 | 1,456 |
| `object` | 2,426 | 1,952 | 27 |
| `pure_candidate` | 29 | 0 | 0 |
| `unknown` | 584 | 1,839 | 1,405 |
| `vfs` | 99 | 481 | 404 |

Fragments group local source shapes. `object_or_state` 1,906, `opaque_boundary` 584, `pointer_or_array` 93, `scalar` 32.

## Assertions and public test inventory

The release parse recorded 5,417 `assert` and 1,041 `testcase` macro expansions across the amalgamation. The separate `SQLITE_DEBUG=1` parse recorded 5,701 and 1,045 respectively. 2,607 of 2,615 release definitions also had a debug definition at the same name and physical offset. Expansion counts include no-op macros in the release parse. The JSON records unowned sites and debug-only definitions separately.

The pinned public source ZIP contains 1,542 `.test` or `.subtest` paths across 12 directories. First-pass test matches include `test/varint.test`, `test/tokenize.test`, `test/select1.test`, `test/func.test`, `test/btree01.test`, `test/pager1.test`, `test/wal.test`, `test/unixexcl.test`. These are inventory matches. The GCC smoke ran, and the upstream test suite remains unrun.

## Representative review targets

| Priority | Region | Entry points | Review scope |
| --- | --- | --- | --- |
| 1 | Scalar and bounded-buffer utilities | sqlite3VarintLen, sqlite3Get4byte, sqlite3Put4byte | Start with explicit byte widths, shift ranges and input/output bounds. |
| 2 | Tokenizer and row decoding | sqlite3GetToken, sqlite3VdbeSerialGet | Model token lookahead, buffer extent and Mem ownership before following VM dispatch. |
| 3 | B-tree and page cache | sqlite3BtreePayload, sqlite3PagerGet | Track cursor state, page pinning, sharing and error paths. |
| 4 | VFS, locking and callbacks | sqlite3OsRead, sqlite3_mutex_enter | Give method tables and externally supplied behavior explicit contracts. |

Physical `sqlite3.c` positions and measured local evidence for sampled definitions.

| Function | Line | Section | Call sites | Local tags |
| --- | ---: | --- | ---: | --- |
| `sqlite3VarintLen` | 38,581 | `util.c` | 0 | pure_candidate |
| `sqlite3Get4byte` | 38,591 | `util.c` | 0 | buffer |
| `sqlite3Put4byte` | 38,613 | `util.c` | 0 | buffer |
| `sqlite3GetToken` | 187,252 | `tokenize.c` | 1 | buffer, globals |
| `keywordCode` | 186,935 | `keywordhash.h` | 0 | buffer, globals |
| `sqlite3Parser` | 186,272 | `parse.c` | 8 | buffer, globals, object |
| `sqlite3VdbeSerialGet` | 91,564 | `vdbeaux.c` | 2 | buffer, globals, object |
| `sqlite3VdbeExec` | 97,179 | `vdbe.c` | 436 | allocator, buffer, callback, globals, object, unknown |
| `lengthFunc` | 134,379 | `func.c` | 6 | buffer, object |
| `sqlite3BtreePayload` | 78,104 | `btree.c` | 1 | buffer, object |
| `sqlite3PagerGet` | 64,747 | `pager.c` | 1 | callback, object, unknown |
| `sqlite3OsRead` | 27,753 | `os.c` | 1 | callback, object, unknown, vfs |
| `sqlite3_mutex_enter` | 30,692 | `mutex.c` | 1 | callback, globals, locks, object, unknown |
| `posixIoFinderImpl` | 46,503 | `os_unix.c` | 0 | buffer, globals, object |
| `sqlite3_sourceid` | 271,129 | `sqlite3.c` | 0 | buffer |

### Source spot checks

- `sqlite3VarintLen` shifts a scalar by seven in a loop. Its `assert(i<10)` appears in both macro inventories. `sqlite3Get4byte` and `sqlite3Put4byte` index four bytes in the Clang branch. GCC selects the `memcpy` and byte-swap path under the same feature flags.
- `sqlite3GetToken` calls `keywordCode`, an internal definition from the generated `keywordhash.h`. `sqlite3Parser` is a Lemon-generated body mapped to `parse.c`. These exercises cover an embedded header definition and a generated C definition.
- `sqlite3VdbeSerialGet` reads a byte buffer and updates a `Mem` record via fields such as `flags` and `u.i`. `lengthFunc` calls value and result APIs. `sqlite3VdbeExec` combines direct calls with dispatches such as the connection's `xProgress` callback.
- `sqlite3BtreePayload` calls `accessPayload` directly. Its buffer and object tags are local. Allocation, locking and VFS tags arrive through direct graph reachability. `sqlite3PagerGet` calls `Pager.xGet`, which stays unresolved.
- `sqlite3OsRead` dispatches `id->pMethods->xRead`. The field declaration comes from embedded `sqlite3.h`, and Clang places `xRead` at bit offset 128 in `sqlite3_io_methods`. `sqlite3_mutex_enter` dispatches through the global mutex configuration. Neither dispatch yields a callee definition in this graph.
- `posixIoFinderImpl` comes from an `IOMETHODS` expansion in `os_unix.c`. Its definition uses the expansion position and the token-pasted identifier. This libclang returned no file-backed spelling location. `sqlite3_sourceid` comes from the generated trailer after the last embedded file.

The source locations above refer to the pinned release amalgamation. The generation scripts and input grammar can be reviewed in the matching Fossil check-in. [SQLite source check-in](https://sqlite.org/src/info/555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76) · [Amalgamation format](https://sqlite.org/amalgamation.html)
