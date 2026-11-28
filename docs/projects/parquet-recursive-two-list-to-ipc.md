# Native Arrow IPC from checked two-LIST Parquet groups

The bridge opens the checked two-LIST Parquet profile and reads every
original group in footer order. It passes the resulting logical batches
to the existing recursive Arrow V5 stream writer. The source profile
is unindexed PLAIN V1/V2 with identity or Snappy and one top-level LIST
of LISTs of signed INT32 or INT64.
[Page checks](parquet-recursive-two-list-v2.md) · [Snappy](parquet-recursive-two-list-snappy.md) · [Logical batches](parquet-recursive-two-list-rows.md) · [Direct events](parquet-recursive-two-list-events.md)

Selection uses the same two cases as direct Events. `Selection.field`
emits the original names, nullability and complete nested field.
`Selection.empty` emits a zero-column schema and one zero-column
RecordBatch with the original row count for each group. A schema-only
source emits its selected schema and EOS. This projection addresses only
the top-level field.

Successful conversion has a checked native readback with the exact
selected schema and ordered batch observations, followed by the modern
eight-byte EOS at the end of the emitted stream. Every input batch
has its original `Rows.GroupWire` witness. The event agreement theorem
equates the selected declarations, full ordered batch observations and
EOS with the direct TwoList event route.
[Existing recursive stream writer](arrow-recursive-stream-writer.md)

Source reads finish before IPC admission. An open failure carries the
original footer or schema error. The first failed group carries its
ordinal and original error, including the page address and incoming
cursor when present. It takes precedence under every IPC budget and
produces no output bytes. The direct Events route retains the complete
earlier groups under either selection.

## Fixtures and regressions

Pinned PyArrow creates the two signed input widths with null and empty
values at both LIST levels, null elements, and signed endpoints. The
bridge checks the labeled V1 reframings with repetition-one and
repetition-two page starts. PyArrow reads ten complete Lean outputs,
including schema-only and zero-column streams. Independent IPC framing
inspection checks every batch count and the final EOS. The native
reader refuses an appended second EOS and an incomplete EOS at the
original terminal address.

The late continuation and CRC controls retain exact original addresses
and completed Events prefixes of `[3]` and `[3, 4]` under both
projections. A zero IPC budget refuses a valid source at the writer
and preserves the original source error on each corrupted input.
[Producer, source and output pins](../../scripts/parquet-recursive-two-list-to-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-to-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-to-ipc-oracle/check.py
~~~
