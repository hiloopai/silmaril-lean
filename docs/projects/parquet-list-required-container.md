# Required Parquet LIST of nullable INT32

`ListFile.RequiredContainer.convert` binds one canonical three-level LIST
column from its original checked footer. The outer LIST is required and its
modern LIST annotation is checked. The repeated `list` node and optional physical
INT32 `element` are checked at their original schema positions. The selected
physical column is ordinal 0. Each row group uses one complete local,
uncompressed PLAIN Data Page V1 frame with Hybrid RLE level sections and no
stored CRC. The existing optional-container entry points retain their own
admission conditions.
[Parquet LIST schema](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#lists) · [Original optional LIST profile](parquet-list-file.md)

## Raw levels and required parents

| Repetition | Definition | Meaning |
| --- | --- | --- |
| 0 | 0 | Empty present list |
| 0 or 1 | 1 | First or next null element |
| 0 or 1 | 2 | First or next signed INT32 element |

The required container contributes no definition level. The maximum
definition level is 2. The decoder refuses a higher definition before
reading scalars, a repetition-1 empty marker, and a leading continuation
with no open list. It consumes both exact level extents and the untouched
PLAIN suffix. The source schema selects the interpretation of definition
zero. The optional-container schema is refused at admission.

The group proof ties the original Snapshot, footer group, chunk and frame
to the checked slot and row totals. The raw event witness has no null
parent case, so every reconstructed list is present. Empty lists and null
INT32 elements stay distinct. A late failure reports its original group
ordinal, frame ordinal and absolute header offset. It retains earlier
batches and takes precedence over any writer refusal.

Successful conversion preserves the original field names and emits a
nonnullable Arrow LIST parent with a nullable child. The checked V5
readback admits that exact schema, all parent validity bits, the ordered
child slots and the exact EOS. A required Arrow parent with a null slot
fails native readback.

## Independent producer

PyArrow 26.0.1 writes the two-group required file and an optional-parent
control containing a null list. Thrift checks the original LIST annotation,
repetition flags, each singleton V1 header and all section extents.
The comparator reads the signed values and nested slots independently.
PyArrow verifies the emitted Arrow field flags, two batches and row values.
An EOS check accounts for every IPC frame. Labeled byte mutations test
the out-of-range definition, a continuation of an empty list, and a
leading continuation in the second group. A zero IPC row cap checks
source-first precedence in each case.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Fixture hashes and observations](../../scripts/parquet-list-required-container/observations.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ListFile.RequiredContainer.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.RequiredContainer.Examples
replay=$(mktemp -d)
python3 scripts/parquet-list-required-container/Oracle.py "$replay" |
  diff -u scripts/parquet-list-required-container/observations.txt -
```
