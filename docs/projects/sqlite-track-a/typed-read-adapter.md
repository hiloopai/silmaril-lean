# Typed SQLite Track A read adapter

Import `Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms`. The adapter uses
the read from PR #3555 at `852fe2dcb8628565856abe1074273abd96ce27ff` and
the interaction API from PR #3543 at
`61d4a44f4514730e0779c4180a768abc21086ed7`.
[Concrete read](read-case.md) · [Pinned interaction API](https://github.com/hiloopai/silmaril-lean/blob/61d4a44f4514730e0779c4180a768abc21086ed7/Silmaril/Semantics/TrackA/Interaction/Defs.lean)

The staged tree issues a typed Pager acquisition. `Coalgebra.handle` runs
`PageRead.Acquire.acquire` to answer it. The resulting bytes or error feed
the staged leaf continuation. The composed tree lowers the acquisition
to a cache check and, on an admitted vacant miss, a visible VFS read.
`Coalgebra.handle` runs the backing VFS handler on that request, records its
completed exchange, and passes the actual reply through `PageRead.accept`
to the VM leaf continuation. On a cache hit the continuation receives the
resident bytes without a VFS request. The handler state holds the file and
completed exchanges. The continuation returns the seek result and cache.
[Typed trees and handlers](../../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Defs.lean)

`interpretations_agree` applies to any backing handler, starting file and
cache, requested slot and page, and `Int64` key. Both handled trees reach
the exact `Read.runStaged` outcome, including file and cache poststates and
the completed request-indexed exchange list. The list validates the file
transition against the backing handler and labels a complete observation of
the open VFS tree. `lowered_observations_eq` gives equality of the full sets
of complete open VFS observations when the lowered tree uses the staged
lookup or the VM leaf continuation. Open observations can also follow
other well-typed VFS replies. The backing-specific theorem selects its
actual reply.
[Public statements](../../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Thms.lean)

The fixtures execute both handled trees on a packed leaf containing rowid
42 with value 7. They check a present key and an absent key with the exact
full target-page exchange when cold and no exchange when warm. An ordinary
I/O error or short read returns a typed error. The pinned C main-file path
can proceed with zero-filled short-read bytes. The comparison is between
the Lean read models, scoped to one target page. C or native refinement,
transaction setup, and multi-page SQL are outside its scope.
[Checks](../../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Checks.lean) · [Pinned C path evidence](https://github.com/hiloopai/silmaril-lean/blob/627432c060169951a08c2454b1c524831ce48793/docs/projects/sqlite-track-a/header-inventory/operations.md)

```sh
lake build --wfail +Silmaril.Semantics.TrackA.Interaction.Thms \
  +Silmaril.Machine.SQLite.TrackA.Read.Checks \
  +Silmaril.Machine.SQLite.TrackA.Read.Adapter.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SQLite.TrackA.Read.Adapter.Checks
for module in Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs \
    Silmaril.Proofs.Machine.SQLite.TrackA.Read.Adapter.Correspondence \
    Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean || exit 1
done
```
