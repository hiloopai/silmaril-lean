# Selected V2 Parquet DATE mixed-codec dispatch

`Parquet.Date.Leaf.MixedCodec.V2` opens one checked snapshot and binds one
flat INT32 DATE leaf by physical ordinal. For each original footer group,
it reads the selected column's codec ID. ID 2 selects GZIP and ID 6 selects
Zstandard. Each route returns the existing V2 dispatcher's result, including
its typed setup, header or decode error. Other IDs return `unsupportedCodec`
with the original ID before the group payload is read. The codec-specific
limits apply to the selected route. The snapshot and native Date32 IPC
have their own limits.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/MixedCodec/V2/Defs.lean)

Both routes cover strict PLAIN-only, dictionary-only and dictionary-to-PLAIN
V2 groups. Successful reads retain the original selected frame chain, stored
CRC evidence where present, and the exact V2 definition levels and
flag-selected value suffix. The event trace retains every complete group
before the first indexed source error. Native Date32 IPC is emitted after
source EOS and preserves the exact descriptor and each ordered batch of
signed nullable day offsets. The selected DATE Snappy readers cover
dictionary-backed profiles. The two-codec entry point reports Snappy as
`unsupportedCodec 1`. The Zstandard route uses the existing bounded dictionary-free
frame decoder and its strict `distance < Window_Size` condition.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/MixedCodec/V2/Thms.lean) ·
[GZIP V2](parquet-date-gzip-plain-dispatch-v2.md) ·
[Zstandard V2](parquet-date-zstd-dispatch-v2.md)

## Pinned comparison

The mixed-codec file is a labeled assembly of six genuine PyArrow 26.0.1
parents. Thrift reads the original footers and page headers, and the parent
oracles verify stored CRCs and decode the original compression and scalar
payloads independently. Assembly copies the original chunks byte for byte
and relocates their footer offsets. The DATE leaf follows an unannotated
INT32 neighbor. PyArrow checks the resulting DATE column and independently
reads the Lean-emitted Date32 IPC. The fixture covers all six routes, both
V2 value storage flags, signed Int32 endpoints and nulls.

A separate assembly appends a genuine Snappy group. The controls cover
unsupported codec IDs, a GZIP body retagged as Zstandard, stored checksum
failures on each supported codec and the earliest failure when both are
damaged. The controls check the exact source coordinate and completed
prefix while the IPC batch budget is zero.
[Comparator](../../scripts/parquet-date-mixed-codec-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-mixed-codec-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true \
  tests/formats/parquet-date-mixed-codec-v2/Axioms.lean
python3 -I scripts/parquet-date-mixed-codec-v2-oracle/check.py
```
