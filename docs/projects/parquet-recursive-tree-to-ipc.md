# Strict Arrow V5 IPC from recursive Parquet trees

`Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.convert` passes
the [native Tree Events](parquet-recursive-tree-events.md) view
to the shared strict Arrow V5 emitter. The input follows the
Tree reader's repeated signed-leaf adapter. The default view
keeps every field. The standard positional projection also permits
reordering, selecting a subset and selecting zero fields. Each view
validates the original source leaves before projecting its groups.

A successful conversion retains the selected recursive declaration
and writes one RecordBatch per original row group. Physical
zero-row groups contribute a batch. Width-zero batches retain
their original positive row counts. A schema-only source reaches
EOS directly after the declaration. The shared strict reader
checks the emitted stream through the complete EOS envelope at
its exact end.

## Source and target results

The source footer or compiler cause takes precedence over any
target budget. A reached native group refusal returns the original
typed cause and the exact selected observations of earlier complete
groups. A shared occurrence refusal or a leaf payload refusal
retains its native coordinates. Target errors come from the shared
writer after source EOS and complete native group validation.

The certificate ties each selected batch to its original
`Tree.Rows.GroupResult` in footer order. The batch equality applies
the proven positional selection to the native observation. The
group result separately certifies exact native reprojection onto
every original signed leaf stream and retains its physical wire
witnesses. The IPC readback supplies the same ordered selected
observations, the selected declaration and exact EOS.

## Verification

The pinned Parquet sources include genuine PyArrow branching V1/V2
files and multiple top-level LISTs with independent lengths. They
cover renamed nested fields, signed extrema, null and empty LISTs,
null Structs and present all-null Structs. The oracle also checks
schema-only output and a labeled physical zero-row group. PyArrow
readback and independent parsing compare the V5 continuation
frames, schema fields, RecordBatch counts and descriptors, canonical
body bytes, and exact EOS. The Lean reader refuses appended and
truncated EOS at the original terminal address.

The late shared-presence and leaf CRC controls keep the original
selected prefix even with exhausted target budgets. Clean sources
exercise typed target caps for schema depth, batch count, row
count, slots and body bytes.
[Source pins](../../scripts/parquet-recursive-tree-events-oracle/fixtures.json) · [IPC pins](../../scripts/parquet-recursive-tree-to-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-to-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-to-ipc-oracle/check.py
~~~
