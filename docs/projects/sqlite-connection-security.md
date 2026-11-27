# SQLite connection security gates

This page maps the Lean model of the SQLite 3.54.1 gates that decide
whether a connection may load extensions, attach databases writably, start
write transactions, or use functions and virtual tables from the schema. It
follows the advice in [SQLite's security guidance](https://www.sqlite.org/security.html).
Each gate is a Boolean function transcribed from one source branch.
`run` decides a finite client sequence in order, using the flags current at
each position.
[Definitions](../../Silmaril/Machine/SQLite/ConnectionSecurity/Defs.lean) ·
[Theorems](../../Silmaril/Machine/SQLite/ConnectionSecurity/Thms.lean) ·
[Checks](../../Silmaril/Machine/SQLite/ConnectionSecurity/Checks.lean)

The source is the tracked amalgamation `sqlite3.c`, SHA-256
`0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`. It is
built with only `-DSQLITE_THREADSAFE=1` ([recipe](../../corpus/sqlite/build.sh)).
On a fresh connection of the pinned x86-64 `libsqlite3.so`, a read of every
modeled `sqlite3_db_config` option with `-1` returned the values of
`Flags.atOpen Build.pinnedDefault`: trusted schema on, defensive off,
extension loading off, ATTACH write and create on. The pinned `sqlite3`
shell is a different client: it turns trusted schema off, turns defensive
on, and enables both extension-loading paths before running any input.

## Source map

| Gate | Phase | Model | Source |
|---|---|---|---|
| Open-time flags | open | `Flags.atOpen` | [`openDatabase`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L191843) |
| `sqlite3_db_config` flag table | when called | `DbConfigOption.apply` | [aFlagOp](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L189354) |
| Flag PRAGMA | prepare of the PRAGMA | `ClientOp.apply (.pragma ..)` | [`PragTyp_FLAG`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L146474) |
| INNOCUOUS ↔ `SQLITE_FUNC_UNSAFE` | registration | `FunctionFlags.ofCreate` | [`sqlite3CreateFunc`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L190346) |
| Function usability | prepare | `functionUsable` | [`sqlite3ExprFunctionUsable`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L114161), [callers](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L111763) |
| Schema origin (`EP_FromDDL`) | prepare | `Origin`, `Site.fromDdl` | [DbFixer](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L126333), [`bTemp`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L126412), [self-reference](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L112852) |
| Virtual-table risk | `xConnect` | `VtabRisk.configure` | [default](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L163206), [`sqlite3_vtab_config`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L163974) |
| Virtual-table read | prepare | `vtabReadUsable` | [`selectExpander`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L155727) |
| Virtual-table write | prepare | `vtabWriteUsable` | [`vtabIsReadOnly`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L133303) |
| C-API extension load | step | `loadExtensionPermitted .c` | [`sqlite3LoadExtension`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L144300) |
| SQL `load_extension()` | step | `loadExtensionPermitted .sql` | [`loadExt`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L136111), [`sqlite3_enable_load_extension`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L144463) |
| ATTACH slots and open flags | step | `attachSlotAvailable`, `attachOpenFlags` | [`attachFunc`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L126023), [flag masking](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L126064) |
| Write-transaction refusal | step | `decideRequest .beginWrite` | [`OP_Transaction`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L100544) |

## Checked statements

- `functionUsable_eq_false_iff`: the function check fails exactly at a
  schema-originated site, for a DIRECTONLY function, or for a non-INNOCUOUS
  function while trusted schema is off. Outside such sites it passes for
  every flag setting (`functionUsable_of_not_fromDdl`). Turning trusted schema
  off therefore does not stop direct calls (`untrusted_direct_call_usable`).
  TEMP triggers and views are not schema-originated. The virtual-table write
  check still applies inside TEMP triggers (`vtab_write_temp_trigger`).
- `SQLITE_DBCONFIG_ENABLE_LOAD_EXTENSION` writes only the C-API bit. The SQL
  function needs both bits (`loadExtension_sql_needs_c`), so setting the
  option to `0` stops both paths. `sqlite3_enable_load_extension` writes both
  bits. The `small` build has neither path.
- When ATTACH write is off, ATTACH opens read-only and cannot create; when
  ATTACH create is off, it cannot create.
- `run_disabled` and `run_take_disabled`: under `Disabled` (trusted schema
  off, C-API loading off, `query_only` on, ATTACH write off), every finite
  request sequence, and each of its prefixes, attempts no `Effect.Forbidden`.
  Client operations in the sequence must keep the profile. The checks show
  that direct calls and read-only ATTACH are still attempted, and that
  removing `query_only` or the ATTACH restriction lets a forbidden effect
  through. A later `PRAGMA trusted_schema=ON` or `PRAGMA query_only=OFF` does
  not keep the profile.

All theorems depend only on `propext`.

## Boundary

These statements are about the transcribed gates. A passing gate is an
attempted effect, not a committed one. The following are not modeled and
remain obligations:

- a refinement to the C source or the pinned ELF;
- the parser and code generator that produce requests and their sites,
  including subprograms;
- the authorizer, which could make PRAGMA settings durable against later SQL;
- automatic reprepare after expiry, which is when prepare gates run again
  under the current flags;
- `sqlite3ParseUri`, VFS behaviour, and b-tree read-only refusal;
- raw SQL and database bytes;
- the bodies of function, virtual-table and progress callbacks;
- flags such as defensive, beyond carrying their bit.

The model does not refer to the
[VM isolation](../../Silmaril/Machine/SQLite/VirtualMachine/Isolation/Defs.lean)
or [write-path](../../Silmaril/Machine/SqliteVfs/TrackA/Write/Defs.lean)
models.
