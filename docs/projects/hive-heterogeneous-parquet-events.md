# Ordered Hive manifest over heterogeneous Parquet Events

`Hive.Manifest.Heterogeneous.readAll` takes an ordered list of literal
relative paths paired with immutable Parquet bytes. The caller declares
the physical fields by zero-based leaf ordinal, name, nullability and
type, and declares the partition schema separately. The adapter binds
all selected physical fields through `FlatProjection.Events` and
checks that each file agrees with the declared schema. The output lists
physical fields in request order and virtual fields in partition schema
order. Repeated paths and field positions retain their occurrences.
The caller supplies the manifest and schema from outside this API.

The adapter uses the default Hive URI directory parser and typed binding
for nullable or required INT32 and UTF8 path constants. It preserves the
literal filename. Missing keys and explicit nulls follow the declared
policy and configured Hive options. A required virtual column refuses
both an explicit null marker and a synthesized null. Duplicate or
unknown keys, invalid signed decimal INT32, and collisions with any
physical leaf are refused. This slice supports INT32 and UTF8 partition
declarations. TIMESTAMP columns come from physical modern Parquet leaves
and retain their independent unit and UTC/local descriptor.

The dataset checks the declared schema once, then binds and reads each
reached file in order. It opens one checked snapshot per occurrence of
a file. Each completed group receives the file's typed constants.
The trace preserves the explicit group row count at any selected width.
A path, open or read failure identifies the original manifest index
and literal path. A read failure also retains the original Parquet
group, output position, physical column and decoder cause. The trace
keeps all earlier files and the completed groups of the failing file.

## Laws and projection

The laws relate every successful file to an independent
`FlatProjection.Events.readAll` call and the shared Hive typed binding.
At dataset EOS those per-file batches concatenate in the supplied order.
The first-error law retains the full earlier prefix. Logical projection
commutes with the existing ordered Hive scan and preserves its terminal
outcome and every batch row count, including at width zero. The projection
uses the declared physical selection. Changing that declaration can skip
an omitted physical fault and reach EOS.

[Public laws](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Heterogeneous/Thms.lean) ·
[Typed Hive binding](hive-typed-partitions.md) ·
[Physical projection](parquet-timestamp-heterogeneous-events.md)

## Independent comparison

Pinned PyArrow writes three genuine Parquet V1/V2 files in Hive-style
paths. Its Hive partition formatter produces the directories and its
dataset parser independently recovers their typed keys, including a
URI-escaped Unicode string with a slash, an explicit null marker and
an absent optional key. PyArrow reads the physical groups and compares
their values, schema and row counts in the supplied order, including one
repeated path. Tests cover reordered and repeated fields, virtual-only
reads, width zero and an empty manifest.

The labeled error case changes one byte of a Zstandard TIMESTAMP
dictionary in the second manifest file at group 1. Lean retains the first
file and group 0 of the second, and reports the original dictionary offset
and typed cause. Logical projection omitting the damaged column retains
that failure. A narrower physical declaration reads all files. Separate
controls exercise missing and required-null partition keys, out-of-range
INT32 text, an unselected collision and a mismatched physical timezone.

[Comparator](../../scripts/hive-heterogeneous-parquet-events-oracle/check.py) ·
[Fixture hashes](../../scripts/hive-heterogeneous-parquet-events-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/hive-heterogeneous-parquet-events-oracle/Axioms.lean
python3 -m venv /tmp/hive-heterogeneous-parquet-events
/tmp/hive-heterogeneous-parquet-events/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/hive-heterogeneous-parquet-events/bin/python -I scripts/hive-heterogeneous-parquet-events-oracle/check.py
```
