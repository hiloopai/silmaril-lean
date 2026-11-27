# Selected PLAIN V2 Parquet DATE with Zstandard

`Parquet.Date.Leaf.Zstd.V2` uses the existing strict checked flat DATE
snapshot and binds one physical INT32 ordinal. It admits codec 6 PLAIN
Data Page V2 and reuses the checked chunk planner and Zstandard scalar
decoder. The original chunk span, page order and footer slot counts
are checked before decoding bodies. Stored and expanded bounds apply
independently. The V1, GZIP and default APIs keep their existing admission.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Zstd/V2/Defs.lean) ·
[Selected V1 DATE](parquet-date-zstd-v1.md)

The decoder checks any stored Parquet CRC on the entire original payload
before splitting its uncompressed definition-level prefix from the scalar
suffix. The resolved V2 compression flag selects one dictionary-free
Zstandard frame or the exact raw suffix. The wire theorem retains
the original prefix bytes and checked presence mask, both declared suffix
extents, the selected decoding relation and the exact signed nullable
slots. It also relates the decoded slot and present counts to the V2
header. Required fields have no levels or nulls. This profile shares the
decoder's strict `distance < Window_Size` condition.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Zstd/V2/Thms.lean) ·
[Flat INT32 Zstandard](parquet-flat-zstd.md) ·
[Parquet page header IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L662-L719)

Native Date32 IPC preserves the leaf name and nullability and emits one
batch per footer group in order through EOS. The first failed group
retains the complete earlier event prefix and its original typed cause.
A source failure takes precedence over IPC writer limits.

## Pinned comparison

Three genuine PyArrow 26.0.1 Parquet files cover required and nullable
DATE, negative days and both signed endpoints, and pages with and
without stored CRCs. Both V2 flag values occur in the producer files.
A raw-only nullable file includes an all-null page with an empty scalar
suffix and passes with a zero Zstandard window budget. Thrift reads
the headers, zlib verifies the CRC, and libzstd 1.5.7 identifies the
exact compressed frame extent. PyArrow checks both the original rows
and Lean-emitted IPC.

The typed controls include separately labeled header and payload
mutations for both wrong flag directions, incorrect levels and null
counts, corruption of the original checksummed levels, and bad
Zstandard magic with a recomputed stored CRC. Low-cap controls pin
the stored-cap, CRC and expansion ordering. Genuine V1 and dictionary
files exercise the V2 profile refusals.
[Comparator](../../scripts/parquet-date-zstd-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-zstd-v2-oracle/fixtures.json) ·
[libzstd 1.5.7](https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-zstd-v2/Axioms.lean
python3 -I scripts/parquet-date-zstd-v2-oracle/check.py
```
