# Checked Parquet LIST to native Arrow IPC

`Parquet.ListFile.Multi.ToIpc.convert` combines the existing canonical
nullable INT32 LIST reader and native Arrow V5 LIST writer. It opens
one immutable Parquet snapshot and uses the original bounded
multi-frame group reader. The output field and child names come
from the two checked schema elements. The output is one nullable
Arrow `List` with a nullable signed Int32 child.
[Parquet admission](parquet-list-file.md) · [V1 frame continuation](parquet-list-continuation.md) · [Native writer profile](arrow-list-int32-writer.md)

The result carries the exact original Parquet event trace and an
`Except` carrying either a native IPC byte string or a typed cause.
The writer runs after the trace reaches EOS. Each successful
Parquet group becomes one IPC record batch in footer order,
including an admitted zero-row group. Null lists, empty lists,
individual null children, and signed values retain their order.
An empty group sequence emits only the schema and EOS.

A read failure preserves all earlier events and the first original
group error, including the frame ordinal and offset when present.
A source read failure takes precedence over writer admission.
Writer refusals retain the successful source trace. Neither failure
returns an IPC carrier. The bridge materializes the source trace
before applying the native writer budgets and does not emit an IPC
prefix. Both source and writer retain their existing admission rules.

`convert_trace` identifies the retained trace with the original
reader. `convert_readback` links the checked footer and exact frame
witness of every group to the native field descriptor, nested slots,
and exact IPC frame chain through EOS. `convert_first_error`
identifies the original prefix and first indexed failure. The
nullable slot equality and native frame witness connect both
validity bitmaps, normalized parent offsets, and child order to
the original Parquet rows.
[Public theorem contracts](../../Silmaril/Formats/Parquet/ListFile/Multi/ToIpc/Thms.lean)

## Pinned comparison

PyArrow 26.0.1 supplies the native two-group PLAIN V1 input and
independently reads Lean's native IPC output. This fixture includes
both signed INT32 endpoints, null and empty lists, and nullable
children. The prior spec-authored continuation file starts its
fourth V1 frame inside an open list. Both PyArrow and Lean's IPC
output give the same complete list.

The empty controls include a native schema-only Parquet file and
an authored zero-row group inserted between the two untouched
producer page bodies. That group uses a real, uncompressed V1
frame with two zero-length level sections and an empty value
suffix. Thrift 0.25.0 checks its original header, footer counts
and bounds. PyArrow reads the zero-row group, and the native IPC
output includes the empty batch in the middle. PyArrow's ordinary
empty-table file with an unframed zero-byte chunk remains a typed
footer refusal in this profile.

A same-length mutation starts the second group's first page with
a continuation. Its original header and chunk stay in place.
Lean retains the first batch, reports the typed group 1/frame 0
continuation error, and yields no IPC bytes even under a writer
budget that would independently fail. The oracle pins the source
and destination byte hashes, exact input frames, ordered nullable
readback, child totals, and exact EOS windows.
[Oracle and wire observations](../../scripts/parquet-list-to-ipc/observations.txt) · [Pinned producer dependencies](parquet-column-index.md#pinned-independent-fixture)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Examples
python3 scripts/parquet-list-to-ipc/Oracle.py "$replay" |
  diff -u scripts/parquet-list-to-ipc/observations.txt -
```
