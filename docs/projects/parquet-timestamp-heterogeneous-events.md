# Ordered heterogeneous Parquet to typed Arrow Events

`FlatProjection.Events.readAll` opens one checked flat Parquet snapshot
and selects INT32, annotated UTF8 and modern INT64 TIMESTAMP leaves in
one ordered projection. Ordinals are zero-based leaf and chunk positions,
as in FlatProjection. Repeat a position to emit it more than once. An empty
selection keeps the original footer group boundaries and row counts.

The Events schema retains each selected name, nullability and value type.
A TIMESTAMP field also retains its original unit and the Arrow UTC or absent
timezone descriptor. Its values are signed ticks at that unit. INT32 and UTF8
come from the existing PLAIN V1/V2 uncompressed primitive paths. They retain
those paths' restrictions on checksums, offsets, and encodings. The UTF8
route additionally requires a valid STRING or converted UTF8 annotation and
validates each present string. The TIMESTAMP route uses the modern binder and
the existing AllCodecs group reader with its codec and page limits. File bytes,
total rows, groups, selected width and shared group row counts are bounded
before the relevant reads.

Each group obtains its row count once from the checked footer. The reader
decodes one column at a time in request order and emits a typed, aligned batch
only when the whole group succeeds. A column error reports the original group,
original leaf ordinal, projection position and typed branch cause. The stream
retains every complete earlier batch. This API emits typed Events.

## Laws

The opened bindings name the original requested positions of the single
checked snapshot. Successful batches agree with each bound column's original
typed reader and the original footer group count. After wider EOS, a physical
projection of the checked bindings gives the same batches and Events observation
as a logical Arrow scan with the corresponding positional projection. On
failure, logical projection keeps the wider error. A physical projection still
agrees on all previously completed groups and determines its own suffix,
which can reach EOS when the fault is in an omitted column.

[Public laws](../../Silmaril/Formats/Parquet/FlatProjection/Events/Thms.lean) ·
[Timestamp routes](parquet-timestamp-all-dictionary-v1.md) ·
[Pinned Parquet Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

## Independent comparison

Pinned PyArrow 26.0.1 writes genuine V1 and V2 files with required INT32,
nullable Unicode UTF8, nullable UTC nanosecond TIMESTAMP (Zstandard
dictionary), and required local microsecond TIMESTAMP (Snappy PLAIN).
PyArrow independently reads typed values, including signed endpoints, nulls
and empty strings. Thrift checks original annotations, page kinds, encodings,
codec IDs, and chunk spans. The comparison covers row groups of 5, 3 and 2 rows,
schema-only input, reordering, duplicates, and width zero. A genuine
checksummed producer file and a genuine unannotated binary schema exercise
the primitive checksum and UTF8 binding refusals.

The labeled late-error fixture changes one byte of the original Zstandard
dictionary frame magic in group 1. It preserves header, extent and footer
bytes. PyArrow refuses the selected chunk. Lean reports the indexed original
`badMagic` cause and retains exactly group 0. Reordering changes the reported
projection position. A narrower physical selection reaches EOS, while logical
projection of the failed trace retains the original error.

[Comparator](../../scripts/parquet-timestamp-heterogeneous-events-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-heterogeneous-events-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.FlatProjection.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-heterogeneous-events-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-heterogeneous-events
/tmp/parquet-timestamp-heterogeneous-events/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-heterogeneous-events/bin/python -I scripts/parquet-timestamp-heterogeneous-events-oracle/check.py
```
