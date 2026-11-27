# Native Arrow IPC from a checked flat Parquet projection

`Parquet.FlatProjection.convert parquet ipc input ordinals` takes an
immutable Parquet carrier and a list of original zero-based physical
leaf ordinals. Successful binding uses one checked snapshot and takes
each selected field's exact name, physical kind and required or optional
layout from the footer. The projection order determines IPC field order.
A repeated ordinal is emitted again at its requested position.

Selected fields admit flat uncompressed PLAIN V1 or V2 INT32 and
BYTE_ARRAY data pages under the existing checked reader profile.
BYTE_ARRAY slots become BinaryView with their exact opaque octets.
Unselected chunks are subject to footer validation and their page bodies
are left unread. Other physical kinds can be present in the footer.
An empty projection emits row counts from the checked footer without
reading column bodies.

Source byte, total row, per-group row and field caps apply independently
of the IPC writer's limits. One complete original group becomes one
ordered RecordBatch. The checked page walk concatenates each selected
column's independent page cuts in source order. A footer with no groups
produces a schema-only stream. An admitted zero-row group produces an
explicit empty batch. The empty-group fixture frames PyArrow's zero-slot
chunks with actual V2 pages to exercise the existing reader policy.

A selected read failure returns its original group, projection position and physical
column ordinal, with the underlying decoder or framing cause. Exhaustion
precedes IPC emission, and the indexed group reader is available for
individual group reads. `bound_read_exact` relates the output columns to
the original frames and decoded slots. `convert_readback` proves exact
native V5 readback of the ordered descriptors and batches through EOS.
[Theorems][laws]

The [oracle][oracle] uses a genuine PyArrow 26.0.1 five-leaf file with
two INT32 leaves, two BYTE_ARRAY leaves and one unselected BOOLEAN leaf.
Thrift 0.25.0 checks original physical metadata, extents and page counts
including cuts `[10, 2]` and `[2, 2, 2, 2, 2, 2]` in the same group.
PyArrow checks seven actual Lean-produced IPC streams including reordered,
repeated and empty projections, a framed empty group, schema-only and
unselected damage. A selected late failure retains the exact page index
and header offset even when the writer's field cap would also refuse.

## Positional composition

`Composition.composeOrdinals [3, 0, 1, 2] [2, 1, 2]` yields
`some [1, 0, 1]`. `Composition.project` applies the same positions to
the ordered schema and batch observations. Out-of-range positions
refuse selection. `project_rowCounts` retains all original row counts
and batch boundaries, including an empty selection on an empty group.

`project_compose` assumes that the original and composed projections
both open and exhaust the same immutable source under a common column
policy. The field and total-row admission caps may differ. The proof
uses exact lookup of the same checked bindings and successful column
reads. A wider read can fail on a chunk omitted by the narrower read.
IPC field and cell policies govern downstream emission independently.
[Composition laws][composition-laws]

The [composition oracle][composition-oracle] reuses the five-leaf
producer and checks a wider source failure on an omitted damaged
column, repeated positions, an invalid position, schema-only output,
and an empty selection through `[12, 0, 6]`. A three-field and a
54-cell IPC budget each admit the composed output while refusing
the four-column output of the original successful source read.

### Direct source success

`project_compose_success` derives direct exhaustion from an admitted
direct open and a successful original read. `project_compose_of_caps`
also derives the direct open from explicit file-byte, total-row and
field caps. Both use `SameColumnPolicy`, which requires matching
snapshot, page and value limits. The three source admission caps can
differ. Repeats may make the composed projection wider than the
original, so the field cap applies to the composed list.

The [source success oracle][success-oracle] compares five direct reads
with PyArrow under exact, independently tighter admission caps. It
checks one-under file, row and field refusals, an expanded repeated
selection and a zero-width selection through an empty middle group.
The success theorem is confined to source observations.

```sh
lake build --wfail +Silmaril.Formats.Parquet.FlatProjection.Checks
python3.13 scripts/parquet-flat-projection-oracle/check.py --out /tmp/parquet-flat-projection
```

[laws]: ../../Silmaril/Formats/Parquet/FlatProjection/Thms.lean
[oracle]: ../../scripts/parquet-flat-projection-oracle/check.py
[composition-laws]: ../../Silmaril/Formats/Parquet/FlatProjection/Composition/Thms.lean
[composition-oracle]: ../../scripts/parquet-flat-projection-composition-oracle/check.py
[success-oracle]: ../../scripts/parquet-flat-projection-success-oracle/check.py
