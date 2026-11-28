### Source spot checks

- `sqlite3VarintLen` shifts a scalar by seven in a loop. Its `assert(i<10)` appears in both macro inventories. `sqlite3Get4byte` and `sqlite3Put4byte` index four bytes in the Clang branch. GCC selects the `memcpy` and byte-swap path under the same feature flags.
- `sqlite3GetToken` calls `keywordCode`, an internal definition from the generated `keywordhash.h`. `sqlite3Parser` is a Lemon-generated body mapped to `parse.c`. These exercises cover an embedded header definition and a generated C definition.
- `sqlite3VdbeSerialGet` reads a byte buffer and updates a `Mem` record via fields such as `flags` and `u.i`. `lengthFunc` calls value and result APIs. `sqlite3VdbeExec` combines direct calls with dispatches such as the connection's `xProgress` callback.
- `sqlite3BtreePayload` calls `accessPayload` directly. Its buffer and object tags are local. Allocation, locking and VFS tags arrive through direct graph reachability. `sqlite3PagerGet` calls `Pager.xGet`, which stays unresolved.
- `sqlite3OsRead` dispatches `id->pMethods->xRead`. The field declaration comes from embedded `sqlite3.h`, and Clang places `xRead` at bit offset 128 in `sqlite3_io_methods`. `sqlite3_mutex_enter` dispatches through the global mutex configuration. Neither dispatch yields a callee definition in this graph.
- `posixIoFinderImpl` comes from an `IOMETHODS` expansion in `os_unix.c`. Its definition uses the expansion position and the token-pasted identifier. This libclang returned no file-backed spelling location. `sqlite3_sourceid` comes from the generated trailer after the last embedded file.

The source locations above refer to the pinned release amalgamation. The generation scripts and input grammar can be reviewed in the matching Fossil check-in. [SQLite source check-in](https://sqlite.org/src/info/555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76) · [Amalgamation format](https://sqlite.org/amalgamation.html)
