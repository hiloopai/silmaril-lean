# Nullable INT32/INT64 STRUCT in native Arrow IPC

`Arrow.StructInt32.Stream.readFor .int64` selects a signed INT32 first child
and a signed INT64 second child in an otherwise unchanged nullable STRUCT IPC
V5 profile. `Writer.emitFor .int64` writes the same positional profile.
The schema checks the signed Int payload and its exact bit width at each
position. The logical row type is `Option (Option Int32 × Option Int64)`.
The original `read` and `Writer.emit` entry points select `.int32` and
keep the two-INT32 profile's wire and admission behavior.
[Original STRUCT profile](arrow-struct-int32-stream.md) ·
[Arrow 26.0.1 Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)

Both widths share the checked three-node, five-buffer RecordBatch layout,
parent bitmap, field descriptors, slot validation, limits, and exact EOS.
For the wide child, the reader checks that the descriptor covers the logical
`8 × rowCount` prefix and passes that exact prefix to the repository's raw
signed little-endian codec. The writer uses the corresponding raw encoder,
keeps the wide bitmap separate and uses the shared aligned buffer packer.
The API retains signed `Int64` values through readback.

`readWideColumn_wire` witnesses every original eight-byte word and child
validity bit, including under null parents. A null parent hides its child
values. Each physical child still has its own checked bitmap, extent and
null count. Requiredness applies to present parents. The writer represents a
hidden nullable child with a null and a hidden required child with zero.
Schema-only streams and explicit empty record batches have distinct
observations. `Writer.emitFor_readback` recovers the exact schema and logical
batches through the checked native reader and exact EOS.

The new width matches the existing Parquet `NestedPoint` child order.
An absent parent definition state maps to outer `none`. A present parent
with an absent optional INT64 leaf maps to a present row with a null second
slot, and a present leaf contributes its full-width signed value. The
direct Parquet-to-IPC bridge remains a separate transport.
[Parquet NestedPoint profile](parquet-nested-point.md)

## Reproduce

```sh
lake build --wfail Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-struct-int32-int64-oracle/Axioms.lean
python3 scripts/arrow-struct-int32-int64-oracle/check.py
```

The [SHA-256 pins](../../scripts/arrow-struct-int32-int64-oracle/fixtures.json)
cover eight genuine PyArrow IPC inputs and three labeled byte edits. CPython
3.13.5 and PyArrow 26.0.1 inspect the actual Lean streams and original
producer bytes, including the signed endpoints, out-of-INT32 values, hidden
wide physical words and nulls, and visible required nulls. The comparator
also checks three byte-identical two-INT32 outputs against pins captured on
the merged two-INT32 squash commit and reruns the original typed refusals.
