# Ordered Parquet TIMESTAMP projection to native Arrow IPC

`Timestamp.Leaf.Projection.ToIpc.convert` emits one native Arrow V5
stream from a completed ordered TIMESTAMP Events projection. It uses
the same caller-ordered 1-based Parquet ordinals and the same checked
Snapshot and AllCodecs limits. The bridge preserves each selected
field's name, nullability, time unit, and exact UTC or absent timezone
annotation. Repeated ordinals repeat their fields and tick columns.

The wire profile is flat little-endian Arrow TIMESTAMP with modern
continuation framing, uncompressed record bodies, and either UTC or
an absent timezone. The writer reuses the TIMESTAMP field fragment,
ordered Schema vector serializer, signed 64-bit value codec, validity
bitmap, physical buffer packer, and checked RecordBatch framing.
The reader binds each field in position order. Each record uses the
original declared extent and exactly one field node and two ordered
buffer descriptors per field. The existing TIMESTAMP column decoder
checks each bitmap and its signed values. Non-TIMESTAMP fields,
other timezone labels, dictionaries and compression are outside this
Arrow profile. The source admits the shared Parquet units ms/us/ns.
The standalone Arrow writer and reader also support seconds.

A successful conversion retains one batch per original footer group.
A framed zero-row group produces a batch with zero rows, and a
zero-width selection preserves each explicit group row count. A
schema-only input emits a Schema followed by EOS. The source must
reach EOS before the writer checks any output budget. A source-open
failure or original indexed column failure is returned intact.

The writer certifies emission through the checked ordered reader.
The readback laws recover the exact selected descriptor list and
aligned signed nullable tick columns with their original group row
counts. The original record suffix has a final EOS at the exact end
of the emitted carrier. The Projected Events API and standalone
single-field reader retain their existing admissions.

[Bridge laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Projection/ToIpc/Thms.lean) ·
[Ordered reader laws](../../Silmaril/Formats/Arrow/TimestampStream/Ordered/Thms.lean) ·
[Writer laws](../../Silmaril/Formats/Arrow/TimestampStream/Ordered/Writer/Thms.lean) ·
[Projected Events](parquet-timestamp-events-projection.md) ·
[Pinned Arrow Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) ·
[Pinned Arrow IPC layout](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)

## Independent evidence

The comparator reuses pinned genuine PyArrow 26.0.1 multi-TIMESTAMP
V1 and V2 Parquet files and a genuine schema-only file. It checks
actual Lean-emitted IPC in PyArrow by field position, comparing
ordered descriptors and signed Int64 values against independently
read Parquet columns. It covers reorder, repeated fields, required
local microseconds, nullable UTC milliseconds and nanoseconds,
signed endpoints, and zero-width positive batches. Lean also reads
an independent PyArrow-emitted IPC stream with repeated names.

A labeled assembly inserts a deterministic framed zero-row group
between two native groups. The original nonempty chunks are copied
with their stored bytes intact. Independent Thrift inspection and
PyArrow readback check the source and the zero-row batch, including
at width zero. A labeled late CRC mutation returns its original
typed failure under zero IPC field and batch caps. A physical
selection omitting the damaged column still produces full IPC.
The comparator rejects bytes after EOS and checks writer refusal
for misalignment, required nulls, signed overflow, named timezones
and the zero-width row budget.

[Comparator](../../scripts/parquet-timestamp-projection-ipc-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-projection-ipc-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-projection-ipc-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-projection-ipc
/tmp/parquet-timestamp-projection-ipc/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-projection-ipc/bin/python -I scripts/parquet-timestamp-projection-ipc-oracle/check.py
```
