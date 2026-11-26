# SQLite handle and default VFS resource contracts

Import `Silmaril.Machine.SQLite.Handle.Thms` for the SQLite 3.54.1 handle
profile. `Handle.Step` uses the shared finite `GlobalState.History`.
`Handle.Payload` supplies connection, statement, blob and backup metadata
and retains the caller's payload family for the remaining kinds.
`Handle.contract` lifts the history relation to the shared tagged allocator
store and preserves its raw allocation history. An object token identifies a
lifetime. A tombstone keeps that token reserved after the object is destroyed.
Backing allocations of particular handles are outside the handle relation.
The rendered SQLite API pages were read on 2026-11-26. The release's API
declarations and documentation also appear in its pinned source header.
[Shared history](global-object-state.md) · [Allocator contracts](allocator-resources.md) · [SQLite release][release] · [Pinned API header][api-src]

## Admission and disposal

| Operation | Selected resource observation |
| --- | --- |
| `sqlite3_open` family | Ready connection on success. Error can return null or a live close-only connection. Close-only refers to this modeled surface. SQLite also allows diagnostics such as `sqlite3_errmsg` on the failed handle. [Open API][open] · [Open implementation][open-src] |
| `sqlite3_prepare` family | An owned ready connection admits prepare. No-SQL input, such as an empty string or a comment, can succeed with a null statement and the same history. A prepare error issues no statement. The caller supplies the input classification. [Prepare API][prepare] · [Prepare implementation][prepare-src] |
| `sqlite3_close` and `sqlite3_close_v2` | Both accept null and immediately retire an idle owned connection. When busy, legacy close returns `BUSY` with the same resource history and deferred close returns `OK` and leaves a zombie. Error strings, tracing and virtual-table effects are outside that equality. [Close API][close] · [Busy check and close][close-src] |
| `sqlite3_finalize`, `sqlite3_blob_close`, `sqlite3_backup_finish` | Null is a no-op. An admitted non-null release retires its child even when the reported SQLite status is an error. Release checks the child's linked parent, permits a zombie, and retires an idle zombie. The optional reaped token is an extra observation of the Lean relation. [Finalize API][finalize] · [Finalize implementation][finalize-src] · [Blob close API][blob] · [Blob close implementation][blob-src] · [Backup finish API][backup] · [Zombie cleanup][reap-src] |

`ReleaseStatus` maps `SQLITE_OK` to `.ok` and all other codes actually
returned by a release to `.error`, including any `SQLITE_BUSY` or
`SQLITE_LOCKED` returned by that release. Legacy close has the distinct
`.busy` observation above. For backup, transient `BUSY` and `LOCKED` from
`sqlite3_backup_step` have no effect on the finish result. A stored fatal
error, such as an I/O or out-of-memory error, can surface as `.error` at
finish. The model abstracts the finish status and leaves step outcomes and
the derivation of the finish code outside the relation. [Backup finish API][backup] · [Backup finish implementation][backup-finish-src]

A connection's ownership controls its close and command admission. A child's
ownership controls its release. Its connection links identify the participants
whose state must be consulted. Reachability along a link grants no ownership.
This profile gives the initiating actor ownership of newly issued tokens.
The finish operation checks whether an existing child is owned and uses
connection presence to perform the cleanup.

`open_error_close_only` and `open_ready` distinguish the two admissions.
`prepare_empty_post`, `close_null_iff`, `close_busy_iff`,
`close_deferred_busy`, and `close_idle_destroys` characterize the selected
outcomes. `zombie_no_commands` excludes new commands. `release_requires_owner`
checks ownership, and `release_disposes` applies to all reported statuses.
`final_dependent_reaps_zombie` constructs
the release of a sole blocker and proves both resulting tombstones.
`reap_idle_zombie` forces destruction once the release check sees an idle
zombie. `stale_not_fresh` and `fresh_before` prevent a retired ID from
becoming fresh across later admitted calls.

## Blob and backup participants

The busy predicate observes public statement Vdbes, a selected live blob's
private Vdbe, and an unfinished backup's **source** B-tree membership. The
blob edge represents its attached private Vdbe with a single blocker carried
by the blob token. Statement tokens represent independently prepared public
statements. The profile covers successful `sqlite3_blob_open` and external
`sqlite3_backup_init` calls. Their failure replies and partial cleanup are
outside the relation. The blob profile ends at close and omits operations
that can invalidate or replace the private Vdbe, such as blob reopen. The
source edge of each backup contributes to `Busy`. This abstracts the source
B-tree count to existence in the selected handle graph. The destination edge
separately records a borrow.
[SQLite busy loop][close-src] · [Blob close implementation][blob-src] ·
[Backup initialization and source count][backup-init-src]

The caller keeps both participants distinct and reserves the destination for
the backup from admission through finish. The public backup API requires
avoiding other uses of the destination over that interval. In particular,
`close_borrowed_inapplicable` excludes both close modes while borrowed,
including when the destination has an empty busy set. The destination
therefore stays live through finish in this profile. SQLite finish decrements
the source B-tree count and runs the zombie check on the destination and
source. A live destination makes its check an identity on handle history.
`backup_finish_destination` proves this preservation and the source still
uses the general reaping rule. [Backup API threading and destination rule][backup] · [Backup finish implementation][backup-finish-src]

## Borrowed VFS lookup and composition

The VFS subset models `sqlite3_vfs_find(NULL)` in an initialized profile.
The caller supplies a fixed registry order with distinct IDs that all look
up as live VFS entries. The result borrows the first such ID, or is null
for an empty registry, with the same object and allocation histories.
`find_default_iff` and `find_default_live` give the result and presence
law. `registered_preserved` requires that the registered keys are outside
the transition's writes. Registration, unregistration, named search and
subsequent VFS operations are outside this lookup contract.
[VFS registry API][vfs] · [Default lookup implementation][vfs-src]

To compare with `GlobalState.VfsRoots`, take `history.toObjects.toKinds` as
its kind store and require `roots.registered.map Subtype.val = registry`.
Then `roots.defaultVfs.map Subtype.val` and the borrowed reply both select
`registry.head?`. The kind references in `VfsRoots` certify membership at
kind `.vfs`. `Registered` also requires each referenced entry to be live in
the full history. [Kind store and ordered roots](global-object-state.md#object-store)

`lookup_frame` and `frames` preserve the full history lookup outside the
declared writes. `Contract.seq_frames` composes handle calls and allocator
calls using the same tagged observation. The checks compose a deferred
close with an error-returning finalizer, and compose VFS lookup with a
malloc whose allocation ID has the same value as the borrowed VFS ID.
The scopes use abstract identity and result codes and omit native pointer
realization, full struct refinement, callbacks, concurrency, transactions,
SQL parsing and error diagnostics.

## Build and replay

Use the repository-pinned Lean toolchain. The checks include 23 public
theorem axiom reports, to compare with the repository policy.
[Toolchain](../../../lean-toolchain) · [Axiom policy](../../../policy.toml) ·
[Replay driver](../../../tools/compiler-explorer/Replay.lean)

```bash
set -euo pipefail
root=Silmaril.Machine.SQLite
lake build --wfail +"$root".Handle.Checks +"$root".Allocator.Checks \
  +"$root".GlobalState.Store.Allocator.Checks
make check CHECK_TARGETS="+$root.Handle.Checks"
for module in "$root".Handle.{Defs,Thms,Checks} Silmaril.Proofs.Machine.SQLite.Handle.Laws; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean
done
```

[release]: https://github.com/sqlite/sqlite/commit/57520227c95396ce39ba6ecaac8d475b78dd3964
[api-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in
[open]: https://www.sqlite.org/c3ref/open.html
[open-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L3721-L3746
[prepare]: https://www.sqlite.org/c3ref/prepare.html
[prepare-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/prepare.c#L825-L895
[close]: https://www.sqlite.org/c3ref/close.html
[close-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L1269-L1342
[reap-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L1387-L1425
[finalize]: https://www.sqlite.org/c3ref/finalize.html
[finalize-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeapi.c#L105-L124
[blob]: https://www.sqlite.org/c3ref/blob_close.html
[blob-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeblob.c#L360-L376
[backup]: https://www.sqlite.org/c3ref/backup_finish.html
[backup-init-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c#L189-L219
[backup-finish-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c#L598-L647
[vfs]: https://www.sqlite.org/c3ref/vfs_find.html
[vfs-src]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c#L351-L383
