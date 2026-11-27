# Ordered mixed Arrow IPC to Parquet PLAIN V1

`MixedV1Writer.FromIpc.WithTimestamp.convert` consumes the existing
checked `Arrow.MixedFlat.Timestamp` stream profile and emits one flat
Parquet file. It admits one or more distinct nonempty NUL-free UTF-8
field names, INT32, UTF8, and modern INT64 TIMESTAMP with millisecond,
microsecond or nanosecond units and exact UTC or absent timezone.
UTF8 uses the modern STRING annotation and the compatible UTF8 tag.
TIMESTAMP uses the modern time-unit and adjustment annotation.
Unsupported seconds, invalid or repeated names, and a width of zero
have typed refusals. Admitted values use their original signed counts.

The bridge checks the input byte cap and completes the original IPC
reader through exact EOS before Parquet writer admission. The writer
checks schema and group bounds, field and slot alignment, and required
nulls. It measures the existing INT32, BYTE_ARRAY and TIMESTAMP pages
and assigns their ordered chunk spans before building page bodies.
One bounded Compact footer serializes a physical type code at each
chunk position. The wire has one UNCOMPRESSED PLAIN V1 page per
column in every explicit batch. Empty batches retain framed zero-row
groups. Schema-only input has zero groups.

The writer certifies the file through the existing `FlatProjection.Events`
reader, comparing the ordered field descriptors, signed nullable samples,
UTF-8 strings, and explicit group row counts with the original input.

## Laws

The generalized Compact serializer preserves the previous homogeneous
footer program and both existing primitive pair orders, including their
budget refusals. The bridge laws describe measured chunk placement and
the exact assembled file. Successful conversion witnesses the complete
original IPC through EOS and the exact ordered Parquet Events
observation. Within the input cap, any original IPC error takes
precedence over writer validation.

[Public laws](../../Silmaril/Formats/Parquet/MixedV1Writer/FromIpc/WithTimestamp/Thms.lean) ·
[Mixed IPC profile](parquet-timestamp-heterogeneous-ipc.md) ·
[Single-type ordered writer](arrow-timestamp-ordered-to-parquet.md) ·
[Pinned Parquet Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

## Independent comparison

Pinned PyArrow 26.0.1 emits ten IPC fixtures. Three admitted inputs
cover reordered mixed fields, signed INT32 and INT64 endpoints, nullable
and required columns, a Unicode name, and strings with both empty and
embedded NUL values. PyArrow reads the actual Lean Parquet files with
group counts of 5, 0 and 3 rows, 3 and 0 rows, and zero groups.
Independent Thrift inspection checks the original column physical
codes, modern and compatibility annotations, chunk and page extents,
definition masks, and each raw signed word or UTF-8 value.

The 20 typed refusals include genuine required-field null and
unsupported unit inputs, invalid names and shapes, and writer budgets.
Two labeled trailing-byte mutations preserve the original indexed IPC
error ahead of writer limits or unsupported seconds.

[Comparator](../../scripts/arrow-heterogeneous-to-parquet-oracle/check.py) ·
[Fixture hashes](../../scripts/arrow-heterogeneous-to-parquet-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-heterogeneous-to-parquet-oracle/Axioms.lean
python3 -m venv /tmp/arrow-heterogeneous-to-parquet
/tmp/arrow-heterogeneous-to-parquet/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/arrow-heterogeneous-to-parquet/bin/python -I scripts/arrow-heterogeneous-to-parquet-oracle/check.py
```
