# Checked Parquet NestedPoint to native Arrow STRUCT IPC

`Parquet.NestedPoint.Multi.ToIpc` opens one immutable Parquet snapshot and
binds both original leaf items. The root must contain one optional,
unannotated group with a required unannotated signed INT32 leaf followed by
an optional unannotated signed INT64 leaf. The output retains the parent name,
the ordered child names, and the original repetition flags as Arrow
nullability. The bridge refuses converted or logical leaf annotations.
[Parquet nested profile](parquet-nested-multipage.md) ·
[Native signed STRUCT profile](arrow-struct-int32-int64-stream.md)

The bridge uses the existing bounded `NestedPoint.Multi` group decoder.
That decoder admits the original uncompressed, CRC-free PLAIN V1 pages with
RLE levels and independently checked sibling page cuts. It checks the
original chunk association, extents, headers, row counts and scalar suffixes.
Each successful source group contributes one typed Events batch, including
a zero-row group with admitted frames. A schema-only input has zero batches.

The required first leaf's definition levels are zero for an absent parent and
one for a present value. The optional second leaf uses zero for an absent
parent, one for a present parent with a null child, and two for a present
child value. The decoder aligns the original parent masks before pairing
the signed slots. The bridge preserves outer absence separately from an
independent null wide child. `readGroup_wire` relates this mapping to both
original page-level witnesses and the checked footer row count.
[Parquet definition-level specification](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#nested-encoding)

`readAll` exposes the ordered typed Events. `convert` returns the same
Events with a separate IPC result. A failed source open returns its original
typed error. At the first reached group failure, Events retains every
completed earlier group and the original indexed cause. The writer receives
the source only at EOS, so a failing source produces no IPC under any writer
budget. `convert_readback` connects successful IPC to the same original
footer, group and slot witnesses and verifies exact native V5 Struct EOS.

## Reproduce

```sh
lake build --wfail Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-nested-point-ipc-oracle/Axioms.lean
python3 scripts/parquet-nested-point-ipc-oracle/check.py
```

The [SHA-256 pins](../../scripts/parquet-nested-point-ipc-oracle/fixtures.json)
cover four genuine PyArrow 26.0.1 Parquet inputs, a labeled late definition-level
edit, and a labeled assembly with a constructed explicit empty V1 group and
the original nonempty chunks. CPython 3.13.5 and Thrift 0.25.0 independently
check the footer annotations, sibling page cuts, definition levels and signed
scalar bytes. PyArrow and raw bitmap checks verify the actual Lean IPC
streams, including INT64 endpoints, values outside INT32, empty batches
and exact EOS. The late edit requests an extra wide value from the original
unchanged scalar bytes. It preserves the first complete Events batch and
returns the original indexed short-payload error under zero writer limits.
