# Ordered Arrow TIMESTAMP IPC to Parquet PLAIN V1

`Timestamp.FromIpc.Ordered.convert` reads one complete ordered
Arrow TIMESTAMP IPC V5 stream and writes a modern flat INT64 Parquet
file. The accepted Parquet profile has at least one field, distinct
names in their original order, and millisecond, microsecond or
nanosecond units. Names are nonempty UTF-8 strings without an embedded
NUL and must fit the configured footer byte limits. The exact UTC
timezone maps to adjusted-to-UTC and an absent timezone maps to
local. Seconds and other timezone annotations have typed refusals.
There is no rescaling of admitted signed counts.

The writer reuses the single-leaf TIMESTAMP annotation and PLAIN
V1 page encoders. The shared Compact footer serializer receives
the ordered leaf annotations and measured chunk spans. It writes
one UNCOMPRESSED PLAIN V1 page per column in each group. The group and
chunk budgets and the bounded footer precede page-body allocation.
A schema-only IPC stream becomes a Parquet file with zero groups.
Each explicit batch becomes a separate group, including consecutive
zero-row batches. An empty group still has a real V1 page header per
column. A zero-width IPC schema is refused.

The source byte cap is checked before reading IPC. Within that cap,
the original ordered IPC reader runs through exact EOS before any
Parquet writer validation. The bridge preserves the reader's typed
errors, including malformed required validity and trailing bytes.
The prepared writer also checks field and row shape, required nulls,
page bounds and the signed INT64 domain. The result is released after
the ordered Parquet Events projection reads every output field and
group, matches the complete footer row counts and recovers the same
descriptors and signed nullable tick columns.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/FromIpc/Ordered/Thms.lean) ·
[Ordered IPC reader](parquet-timestamp-projection-ipc.md) ·
[Single-field TIMESTAMP writer](arrow-timestamp-to-parquet.md) ·
[Pinned Parquet encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Pinned Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

## Independent evidence

Pinned PyArrow 26.0.1 emits three admitted IPC fixtures covering
multiple ordered fields, nullable UTC and local values, a required
local microsecond field, signed endpoints, Unicode field names, and
schema-only input. PyArrow reads the actual Lean Parquet files with
group counts of 5, 0, 0 and 3 rows, 3 and 0 rows, and zero groups.
Independent Thrift inspection checks each original PLAIN V1 page
header, UNCOMPRESSED footer extent, TIMESTAMP annotation and
compatibility tag, definition mask, and little-endian signed words.

The 17 typed refusal checks include unsupported and malformed IPC,
invalid names, width, file and group caps, and standalone page-shape
controls. The two labeled trailing-byte mutations keep their
original indexed IPC error under output caps. The seconds mutation
also verifies that full source failure precedes destination unit
validation.

[Comparator](../../scripts/arrow-timestamp-ordered-to-parquet-oracle/check.py) ·
[Fixture hashes](../../scripts/arrow-timestamp-ordered-to-parquet-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-timestamp-ordered-to-parquet-oracle/Axioms.lean
python3 -m venv /tmp/arrow-timestamp-ordered-to-parquet
/tmp/arrow-timestamp-ordered-to-parquet/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/arrow-timestamp-ordered-to-parquet/bin/python -I scripts/arrow-timestamp-ordered-to-parquet-oracle/check.py
```
