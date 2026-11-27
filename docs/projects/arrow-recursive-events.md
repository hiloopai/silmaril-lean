# Positional Arrow Events for recursive IPC streams

`Arrow.RecursiveSchema.Stream.Events.read` adapts the
[checked recursive stream](arrow-recursive-stream.md) to the shared
`Arrow.Events.EventStream` and `AlignedColumns` types. One complete native
batch becomes one Events batch. Empty batches remain explicit and a
zero-width batch retains the original row count.

The position is the identity used for selection. Each position carries the
original optional name and full recursive Field declaration. An absent name,
an explicitly empty string, and repeated names retain their original meanings
and positions. Present cells are indexed by that declaration and carry the
source `CellFits` proof. The original `RowFits` witness supplies each cell
and its nullability. `declarations_signature`, `eraseRow_ofRow`, and
`eraseBatches_ofTrace` recover the exact source declarations and batches in
order.

Schema-open errors retain the original typed cause outside an Events trace.
An opened stream emits its complete batches and then either EOS or the first
reached read error, with the original ordinal, byte offset, and stage cause.
`read_wire` binds these results to the original `Stream.TraceWire`.
`read_failure` ties a read error to the original failure witness and complete
prefix. `read_eos` binds Events EOS to the modern marker at the exact end.

`readProjected` and `projectTrace` use `Scan.Projection.projectColumns`.
A projection can reorder, repeat, or omit positions, including choosing
zero positions. It preserves each row count, the batch sequence, and the
original terminal result. Projection runs on the complete decoded event
prefix, so omitting a column preserves a reached failure in that column.
The identity and composition laws hold on traces. `projectTrace_rows`
agrees with projecting the ordered shared row observation.

The adapter inherits the modern little-endian uncompressed V5 profile for
signed INT32, signed INT64, Struct, and List, together with the native
schema, frame and slot budgets. It consumes a supplied IPC carrier and
adapts its checked trace.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-recursive-events-oracle/Axioms.lean
python3 scripts/arrow-recursive-events-oracle/check.py
```

The pinned PyArrow comparison uses positional columns, including the
genuine repeated names in the four-level fixture. It checks empty and
zero-width batches, reorder and repeat, identity, composition, and zero
selection. The genuine empty-name List and the separately labeled name-slot
edit distinguish `some ""` from `none`. The late semantic control retains
its original failure under both repeat and zero-width projection. A legacy
stream checks open errors and a labeled late legacy envelope checks the
reached framing error.
[Fixture pins](../../scripts/arrow-recursive-events-oracle/fixtures.json)
