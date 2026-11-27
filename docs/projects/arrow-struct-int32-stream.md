# Nullable two-INT32 STRUCT in native Arrow IPC

`Arrow.StructInt32.Stream` reads one top-level nullable STRUCT with exactly two
signed INT32 leaves in little-endian IPC V5. It retains the parent name, ordered
child names, and each child's required or nullable flag. It uses the standard
STRUCT union tag 13 and the same primitive leaf decoder and framed
RecordBatch metadata decoder as the other native IPC profiles. The writer uses
the existing fixed-width buffer encoder and framed RecordBatch writer.
[Arrow 26.0.1 Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) ·
[Arrow 26.0.1 format specification](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)

One row is `Option (Option Int32 × Option Int32)`. The parent bitmap alone
selects a null parent. A parent with two null children is present when both
children are nullable. The reader checks the three equal-length field nodes and
five depth-first buffer descriptors, signed words, and each node's physical
null count. Required child flags apply to visible slots. Hidden child bits and
words may take any values consistent with those physical checks. The writer
uses null for a hidden optional child and zero for a hidden required child.
The reader retains logical rows rather than hidden physical payload.

A schema-only stream has zero batches. Every explicitly framed empty batch
counts toward the batch cap and survives readback. The selected profile uses
three field nodes for the field and total-cell limits. It requires exact modern
EOS. Schema and indexed batch errors distinguish unsupported metadata, node
or descriptor shape, invalid bitmaps, visible required nulls, and limits. The
general flat and LIST entry points keep their existing type admissions.

`read_wire` ties the observation to the original schema slice, nodes, buffers,
and exact terminator. `readRow_absent` and `readRow_present_nulls` give the
two distinct parent-presence outcomes. `Writer.emit_readback` recovers the
exact declared fields and logical batches from emitted IPC through that reader.

## Parquet correspondence

Parquet's separate definition levels become the independent Arrow parent and
child validity bits. An absent optional group maps to no parent. A present group
with an absent optional leaf maps to a present parent with a null at that leaf.
For a required leaf, an admitted present parent must have its signed value.
Sibling streams must first agree on parent presence, as in the existing
`Parquet.NestedPoint.Multi` reader. The current Parquet profile uses a required
INT32 first leaf and an optional INT64 second leaf. Its full-range native
bridge requires checked signed INT64 support in the second Arrow position. The
two-INT32 profile introduces no narrowing conversion.
[Parquet definition levels](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#nested-encoding) ·
[Parquet sibling alignment](parquet-nested-multipage.md)

## Reproduce

```sh
lake build --wfail Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-struct-int32-oracle/Axioms.lean
python3 scripts/arrow-struct-int32-oracle/check.py
```

The [fixture pins](../../scripts/arrow-struct-int32-oracle/fixtures.json) cover
nine genuine PyArrow IPC inputs and six labeled byte edits. CPython 3.13.5 and
PyArrow 26.0.1 check the actual Lean IPC bytes, including three nodes, five
descriptors, the three independently stored bitmaps, signed endpoints,
positional duplicate names, and exact EOS. The positive fixtures include hidden
nonzero words, a hidden physical null under a required child, a present row with
two null children, and zero-row batches. The comparator tests 19 typed refusals.
