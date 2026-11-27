# BinaryView IPC to one PLAIN BYTE_ARRAY group

`Parquet.Plain.ByteArray.FromIpc.convert` accepts one flat BinaryView
field in a modern Arrow IPC V5 stream. It consumes the original carrier
through exact EOS under the IPC and BinaryView reader limits. It then
feeds the ordered nullable octets to the checked unannotated PLAIN V1
BYTE_ARRAY file writer. The field name and required or optional layout
come from the validated IPC schema. Null and present empty remain
distinct. [Source reader](../../Silmaril/Formats/Arrow/BinaryView/Stream/Thms.lean) ·
[Singleton writer](../../Silmaril/Formats/Parquet/PlainByteArrayV1Writer/File/Thms.lean)

The native file has one leaf, one V1 page and one row group. The
converter concatenates all original batch slots in order. Schema-only
input and input with only empty batches both yield one explicit framed
zero-row group. The source admission distinguishes these carriers and
counts empty batches against its batch cap.

The source reader applies its usual signed-i32 view length, buffer index
and offset checks, plus its configured framing, row, batch, buffer and
value limits. The file writer independently applies its aggregate row
cap and one-page row and byte caps to the concatenated rows. The PLAIN
value lengths and page body are below `2^31`, file offsets use the
writer's signed-i64 bound, and the footer length fits its four-byte
trailer. These caps can refuse a file after a successful multi-batch
source read.

`convert_readback` ties the accepted writer input and exact checked
footer to the original stream observation and to the selected read at
column zero and group zero. The failure laws retain the original native
source error before any writer check, including an indexed late error.
Once the source and slot preparation succeed, the writer's original
error is returned at the writer stage.
[Conversion laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/FromIpc/Thms.lean)

PyArrow 26.0.1 writes and reads the pinned IPC producers, then verifies
the field and exact ordered slots from four Lean-emitted Parquet files.
CPython with Thrift 0.25.0 independently checks the physical schema,
chunk offsets, complete V1 header and exact level and scalar bytes.
The fixtures include required and optional inputs, an interior empty
batch, schema-only input, an explicit empty batch, and all 256 octets.
[Comparator](../../scripts/binary-view-to-parquet-oracle/check.py) ·
[Fixture pins](../../scripts/binary-view-to-parquet-oracle/sha256.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc.Checks
python3.13 -B scripts/binary-view-to-parquet-oracle/check.py --out /tmp/binary-view-to-parquet
```
