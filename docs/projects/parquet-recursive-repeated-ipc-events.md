# Native Arrow IPC and direct Events from repeated Parquet

Both routes use the checked recursive repeated row-group reader for
the same unindexed PLAIN V1 signed INT32/INT64 profile with at most
one repeated ancestor on each physical leaf path.
[Repeated row groups](parquet-recursive-repeated-rows.md)

`Parquet.RecursiveSchema.Repeated.Rows.ToIpc.convert` reads every
original group from a compiled source before passing the ordered
observations to the recursive V5 stream writer. A reached source
failure therefore takes precedence over writer admission. On
success, the readback theorem carries the original `Rows.GroupWire`
for each observation and the strict native readback certificate.
This binds all declarations, logical rows, explicit batch counts
and exact terminal EOS. A schema-only original has no batches. An
admitted empty group contributes one zero-row batch.
[Recursive Arrow stream writer](arrow-recursive-stream-writer.md)

`Parquet.RecursiveSchema.Repeated.Rows.Events.read` opens the original
bytes and drives the shared row-group reader. Footer and schema
refusals are open errors. Each completed group emits one shared
positional batch. A reached group failure terminates the trace with
its original group index, cause and physical coordinates. The
prefix theorem binds every completed batch to the original group and
identifies the first reached failure or EOS.

`readProjected` uses shared logical positional projection over the
validated Events. It preserves each count, the original terminal
outcome and projected row order, including at width zero. Projection
supports positional repetition, reordering, identity and composition.
All declared leaves are validated even when the projection omits them.
The agreement theorem relates the direct read of the original carrier
to successful IPC conversion and readback of that carrier's checked
source. It compares declarations, logical batches with their counts,
and EOS.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-repeated-ipc-events-oracle/Axioms.lean
python3 scripts/parquet-recursive-repeated-ipc-events-oracle/check.py
```

Pinned PyArrow independently reads the seven actual Lean streams.
Raw IPC inspection checks the field vectors, native group boundaries
and exact EOS. Direct Events are compared to the input's positional
declarations and logical rows. The fixtures cover null and empty
lists, null elements, present Structs with null children, independent
list sizes, the authored mid-row split and explicit groups of
3, 0 and 2 rows. The two late disagreement edits retain the
complete first group and their original coordinates after zero-width
projection. They also take precedence over zero IPC writer limits.
[Source pins](../../scripts/parquet-recursive-repeated-rows-oracle/fixtures.json) ·
[Emitted IPC pins](../../scripts/parquet-recursive-repeated-ipc-events-oracle/fixtures.json)
