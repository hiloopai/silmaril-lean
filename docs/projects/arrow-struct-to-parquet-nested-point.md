# Native STRUCT IPC to Parquet NestedPoint

`Parquet.NestedPoint.Multi.Writer.FromIpc.convert` reads the checked native
V5 STRUCT IPC profile through exact EOS. The admitted descriptor is one
nullable parent with a required signed INT32 child followed by an optional
signed INT64 child. Both ordered child names and the parent name come from the
source. Empty or NUL-containing names and duplicate sibling names get typed
writer errors. Descriptor and output validation start after the original
IPC source has passed.
[Checked native IPC profile](arrow-struct-int32-int64-stream.md)

The writer measures two uncompressed, CRC-free PLAIN Data Page V1 frames per
group, one per original leaf. The left and right definition levels are
`(0,0)` for an absent parent, `(1,1)` for present with a null INT64
child, and `(1,2)` for present with an INT64 value. The level-pair law uses
the required and optional bindings of `NestedPoint.Multi`. Each leaf has
maximum repetition level zero. Its body uses a length-prefixed RLE
definition section followed by exactly the present signed little-endian words.
Physical child payload masked by the Arrow parent has no logical value.
[NestedPoint definition levels and original group reader](parquet-nested-multipage.md)

The bounded Compact footer describes the original parent and ordered leaves
without annotations. It records each chunk's exact path, position and extent.
An explicit empty IPC batch writes a group with two zero-row frames and empty
definition and scalar sections. A schema-only stream writes zero groups.
Consecutive empty batches preserve their positions. Successful output is
certified by the checked footer and `NestedPoint.Multi` decoder, and
`emit_readback` recovers the exact ordered `ToIpc` Events. A successful
native re-emission with its supplied budgets recovers the original IPC
descriptor and every logical batch through EOS.
[Checked Parquet-to-IPC bridge](parquet-nested-point-to-ipc.md)

## Reproduce

```sh
lake build --wfail Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-nested-point-from-ipc-oracle/Axioms.lean
python3 scripts/parquet-nested-point-from-ipc-oracle/check.py
```

The [input pins](../../scripts/parquet-nested-point-from-ipc-oracle/fixtures.json)
cover nine genuine PyArrow 26.0.1 IPC streams and two labeled trailing-byte
edits. Thrift 0.25.0 and PyArrow independently inspect three actual Lean
Parquet files, including the unannotated nested footer, group and chunk
extents, exact V1 headers and definition-level bytes, signed endpoints and
values outside INT32. PyArrow checks the three returned native IPC streams
with group counts of `[5, 0, 0, 2]`, `[]` and `[0]`. The comparator
checks 13 typed refusals, including late IPC source precedence over both
invalid output limits and unsupported requiredness.
