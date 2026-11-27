# Checked recursive Parquet row groups and Arrow IPC

`Parquet.RecursiveSchema.Rows.readGroup` assembles one original footer
group from its ordered [recursive schema](parquet-recursive-schema.md)
and [checked signed V1 chunks](parquet-recursive-chunk.md). The profile
covers unannotated required and optional groups and signed INT32/INT64
leaves with uncompressed PLAIN Data Page V1 chunks. The compiled shape,
original leaf paths and the chunk profile determine admission.

The footer column count must exactly match the compiled width. Each
original chunk is decoded at its physical ordinal, then indexed once by
group-relative row. The group reader budgets total slots before
decoding, in addition to the column and original chunk limits.
Sibling page cuts can be different. Even an explicit zero-row group
checks all of its original chunks, then yields an observation with
zero rows.

At every group a row's descendant slots must agree on whether their
first absent declaration is that group. The assembler compares the
first physical descendant against each following descendant in order.
A disagreement identifies the original group, row and ancestor
location, with both original column ordinals and paths. An absent
group consumes all of its descendant positions. A present group
recursively assembles every child, preserving the distinction from
a present Struct with all nullable children absent. A null leaf consumes
its own position. The final row must exhaust the assembled evidence.

The row projection relation independently specifies the original
leaf slots of an assembled cell. Successful reads give exact original
column and row ranges, Arrow `RowFits`, and that projection at every
original row ordinal. Each column carries the source chunk witness.
`readAll` follows the original footer group order. The native
`Rows.ToIpc.convert` entry point completes source validation before
calling the [recursive Arrow writer](arrow-recursive-stream-writer.md).
Successful output has the original recursive declaration and one batch
per admitted group, with strict native readback through exact EOS.

## Direct Arrow Events

`Parquet.RecursiveSchema.Rows.Events.read` opens the original Parquet
bytes and uses the shared Parquet row-group reader to emit positional
`Arrow.Events`. It carries the original recursive field declarations
and emits one batch for every complete row group, including zero-row
groups. Footer or schema errors fail at open. After open, a reached
group error terminates the trace at its original ordinal, with the
original error and all earlier complete batches.

The wire theorem relates each batch to the source group's `GroupWire`
and identifies the first reached error or EOS. The IPC agreement theorem
compares the direct and native IPC routes on their declarations, ordered
logical rows, explicit batch counts and EOS when native conversion and
readback succeed.

`readProjected` applies shared positional projection to the validated
Events. It can reorder and repeat positions or produce width zero.
The shared identity and composition laws apply, and every projection
preserves each batch count and the original terminal outcome. All
declared source leaves are checked, including leaves omitted by
projection. The direct adapter uses the same uncompressed PLAIN V1
signed INT32/INT64 profile as the row-group reader.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-rows-oracle/Axioms.lean
python3 scripts/parquet-recursive-rows-oracle/check.py
```

Pinned PyArrow independently reads six actual Lean IPC streams and checks
their ordered nested values, schema, batch boundaries and EOS. The
predecessor files include genuine unequal sibling page cuts and
checksummed chunks. The explicit zero-row assembly inserts one checked
empty group while retaining the original populated chunks. Two labeled
single-level edits preserve per-chunk admission and change only
shared ancestor evidence. Lean identifies the exact outer or inner
group, later row, and conflicting columns. Both source errors preempt
writer admission under zero IPC limits. A separate labeled extra
original column is rejected by the checked footer.
[Fixture pins](../../scripts/parquet-recursive-rows-oracle/fixtures.json)

To check the direct adapter and its shared projection laws:

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-events-oracle/Axioms.lean
python3 scripts/parquet-recursive-events-oracle/check.py
```

The direct oracle reuses the pinned populated, schema-only, multipage,
checksummed and explicit empty-group sources above. PyArrow supplies
expected positional declarations, rows and original group counts.
The same late sibling edits retain group 0 and report the exact group 1
cause after repeated and zero-width projections. The extra-column
footer edit and a genuine annotated LIST file fail before any Events.
[Schema refusal pin](../../scripts/parquet-recursive-schema-oracle/fixtures.json)
