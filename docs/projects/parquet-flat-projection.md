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

```sh
lake build --wfail +Silmaril.Formats.Parquet.FlatProjection.Checks
python3.13 scripts/parquet-flat-projection-oracle/check.py --out /tmp/parquet-flat-projection
```

[laws]: ../../Silmaril/Formats/Parquet/FlatProjection/Thms.lean
[oracle]: ../../scripts/parquet-flat-projection-oracle/check.py
