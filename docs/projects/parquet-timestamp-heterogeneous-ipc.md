# Ordered heterogeneous Parquet projection to native Arrow IPC

`FlatProjection.Events.ToIpc.convert` consumes the checked ordered Parquet
projection and emits a native Arrow IPC stream for INT32, UTF8 and modern
TIMESTAMP. The Parquet reader supplies the exact selected fields, one aligned
batch per group, and the first source failure. The converter checks source
termination before applying any writer limits. A failed source returns its
original typed error, including the group, column, output position and
underlying decoder cause.

The IPC profile uses little-endian V5 Schema and RecordBatch messages, modern
continuation envelopes and exact EOS. The writer reuses primitive and timestamp
field fragments and buffer encoders. The reader uses the normalized Schema
reader, the MixedFlat descriptor assignment and the existing per-field value
decoders. Each timestamp retains its own unit and exact UTC or absent timezone.
The standalone IPC reader and writer support all four Arrow timestamp units.
Parquet sources supply milliseconds, microseconds or nanoseconds.

The writer and checked readback preserve field order, repeated positions,
names, nullability, signed values, valid Unicode strings and explicit batch
row counts at any supported width. Schema-only input and explicit zero-row
batches remain distinct. The configured budgets constrain fields, metadata and
body extents, batches, rows and total cells. Zero-width batches still consume
the row and batch budgets. Named timezones beyond UTC, compression, nested
fields, dictionaries and custom metadata are outside this profile.

## Laws

The bridge preserves every positional schema descriptor and typed column.
The reader's wire relation binds every original record metadata span and
body to its ordered descriptor assignment, and terminates exactly at EOS.
Successful conversion gives the complete source Events observation through
this wire relation. The bridge preserves checked source admission and read
errors before writer validation.

[Bridge laws](../../Silmaril/Formats/Parquet/FlatProjection/Events/ToIpc/Thms.lean) ·
[Reader laws](../../Silmaril/Formats/Arrow/MixedFlat/Timestamp/Thms.lean) ·
[Writer laws](../../Silmaril/Formats/Arrow/MixedFlat/Timestamp/Writer/Thms.lean) ·
[Parquet projection](parquet-timestamp-heterogeneous-events.md)

## Independent comparison

Pinned PyArrow and Thrift validate the original heterogeneous Parquet V1/V2
fixtures. PyArrow reads seven actual Lean IPC outputs through exact EOS and
compares fields and values by position. The checks include signed endpoints,
Unicode, repeated and reordered fields, schema-only, and positive row counts
at width zero. The labeled Parquet assembly preserves the original nonempty
chunks and inserts a framed zero-row group, giving batches of 5, 0 and 3 rows
at both nonzero and zero width.

Lean reads and re-emits two genuine PyArrow IPC streams. One has mixed types,
repeated names with distinct values and an explicit empty batch. The other
has zero width and batch row counts 4, 0 and 2. PyArrow checks both
re-emissions. A genuine named-timezone input and a labeled trailing-byte edit
exercise the reader's typed metadata and EOS refusals. The labeled late
Zstandard source failure retains its original cause even under zero writer
field, batch and row budgets. Selecting only healthy columns emits all groups.

[Comparator](../../scripts/parquet-timestamp-heterogeneous-ipc-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-heterogeneous-ipc-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-heterogeneous-ipc-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-heterogeneous-ipc
/tmp/parquet-timestamp-heterogeneous-ipc/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-heterogeneous-ipc/bin/python -I scripts/parquet-timestamp-heterogeneous-ipc-oracle/check.py
```
