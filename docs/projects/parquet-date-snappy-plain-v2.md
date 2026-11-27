# Selected Snappy PLAIN V2 Parquet DATE

`Parquet.Date.Leaf.Snappy.V2` binds one flat required or optional INT32
DATE leaf by physical ordinal in a checked snapshot. Each selected
chunk uses codec 1 and PLAIN Data Page V2. The shared PLAIN planner
checks the original chunk extent, data offset, group row count, and
independent stored and expanded chunk caps. Dictionary and index
offsets are typed refusals.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Snappy/V2/Defs.lean) ·
[Checked DATE leaf](parquet-date-selected-leaf.md)

The per-page verifier checks the stored size cap and original extent
before checking any stored CRC over the whole payload. Scalar admission
then checks the expanded cap and splits off the original raw definition
levels. The resolved V2 compression flag selects either one complete
bounded Snappy block or the exact literal scalar suffix. The page witness
retains the original PLAIN tag, level and suffix extents and signed
nullable slots, including agreement with the header row and null counts.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Snappy/V2/Thms.lean) ·
[Parquet V2 page header](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L662-L719)

Each original footer group contributes one native Date32 IPC batch.
Successful readback retains the field name, nullability, original order
and signed slots through EOS. The first failed group retains the earlier
complete event batches and the original typed cause. Source processing
precedes IPC writer limits.

## Pinned comparison

Two genuine PyArrow 26.0.1 files cover nullable DATE with CRC and required
DATE without CRC. Both value storage flags occur in both files. The
selected DATE leaf follows an unannotated INT32 column, and the rows
include signed Int32 endpoints. Thrift independently reads the original
footer and page headers, zlib checks the stored CRCs, and PyArrow decodes
the compressed scalar suffixes and independently reads the Lean-emitted
IPC. The pinned controls distinguish original stored corruption from
a wrong Snappy preamble with a recomputed CRC, exercise exact source
coordinates and earlier groups with a zero IPC batch cap, and check
independent byte and row bounds. Genuine Snappy V1, Snappy dictionary,
and GZIP V2 files cover profile refusals.
[Comparator](../../scripts/parquet-date-snappy-plain-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-snappy-plain-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true \
  tests/formats/parquet-date-snappy-plain-v2/Axioms.lean
python3 -I scripts/parquet-date-snappy-plain-v2-oracle/check.py
```
