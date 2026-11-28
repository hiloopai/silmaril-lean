# Checked Arrow IPC to two-LIST Parquet

`Parquet.RecursiveSchema.TwoList.Writer.FromIpc.convert` takes a binary
Arrow V5 stream and runs the existing recursive stream decoder. The
original named LIST of LISTs and its signed INT32 or INT64 leaf supply
the Parquet declaration. Each original ordered record batch becomes one
row group, including a batch with zero rows. A schema-only stream
produces a schema-only file. Nested null and empty lists, null leaves,
and present signed values keep their distinct logical observations.
[Recursive Arrow stream profile](arrow-recursive-stream.md)

The importer uses the checked writer's bounds and geometry. It writes
one unindexed UNCOMPRESSED PLAIN Data Page V1 of complete rows per
group, with optional page CRC. The writer performs checked readback of
the finished file. The importer accepts the complete top-level field
and applies no projection.
[Two-LIST writer profile](parquet-recursive-two-list-writer.md)

## Wire and observation agreements

`convert_readback` binds the exact original schema frame, all ordered
batch frames, and the eight-byte EOS ending at the source extent.
It then binds the writer's construction and Rows and Events readback
to those same declarations and batches. `agrees_events` equates direct
IPC and Parquet Events by declaration, complete batch observations and
EOS. `round_trip` uses the full-field Parquet-to-IPC bridge and proves
that a successful result has the same schema and ordered batches
through its own exact EOS.
[Forward bridge](parquet-recursive-two-list-to-ipc.md) · [Parquet Events](parquet-recursive-two-list-events.md)

The decoder finishes the original stream before target admission.
A schema refusal preserves the original Arrow error. A terminal refusal
retains the complete source prefix and the first failing ordinal,
offset and typed cause. A failed source produces no Parquet bytes,
even when the target budgets are exhausted.

## Verification

Pinned PyArrow produces 18 positive streams across both signed widths
and all eight nullability combinations. They cover renamed fields,
nested nulls and empties, signed extrema, multiple batches, a physical
empty group and a schema-only stream. The independent oracle checks
original Arrow frames, 35 Lean Parquet V1 pages, and 18 returned IPC
streams through exact EOS. PyArrow reads the Lean Parquet groups and
returned IPC, and Lean checks the original trace and direct Rows and
Events readback.

Genuine controls cover legacy framing, one LIST and width zero. Labeled
edits exercise malformed later records, missing and truncated EOS,
trailing input, and another EOS. Seventeen typed checks cover the
original prefix and exact source error, source batch limits and
precedence over target limits, and the checked writer's refusals.
[Producer, input and output pins](../../scripts/parquet-recursive-two-list-from-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-from-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-from-ipc-oracle/check.py
~~~
