# Selected dictionary-free Parquet TIMESTAMP scalar encodings

`Timestamp.Leaf.ScalarDispatch.convert` selects one modern flat INT64
TIMESTAMP leaf through the checked Snapshot. Each selected chunk can
use UNCOMPRESSED (codec 0) or Snappy (codec 1). Its footer encoding list
may contain any union of PLAIN (0), DELTA_BINARY_PACKED (5), and
BYTE_STREAM_SPLIT (9), with at least one value tag and optional RLE (3)
for levels. The page's own value tag must occur in that original footer
list. The footer may advertise additional supported tags. The profile
requires absent dictionary and index page offsets.

The bounded original frame chain and declared group slot total are
checked before page-body decoding. For each original V1 or V2 data page,
a header tag lookup selects one scalar decoder. An unsupported or
undeclared tag is an indexed source error. Each selected decoder
checks the original stored extent and any CRC before reading the body.
V1 applies the original footer codec to the entire stored body before
separating levels. V2 keeps the raw level prefix and uses the effective
codec for the exact value suffix. A false storage flag selects literal
bytes. A true or absent flag uses the footer codec.

The PLAIN branch uses the original signed little-endian words. The
delta branch reconstructs signed INT64 modulo 2^64. The split branch
reassembles eight byte lanes per present signed little-endian word.
Each branch uses the checked original definition mask to preserve nulls
and slot order. Page-body errors retain their original cause, page
ordinal and absolute header offset. The first failed footer group
retains the earlier complete Events and precedes native writer admission.
Successful native Arrow V5 IPC preserves the selected field name,
nullability, unit, UTC or local interpretation and original footer
batches through EOS.

The agreement laws transfer successful homogeneous group results from
the standalone PLAIN, DELTA_BINARY_PACKED and BYTE_STREAM_SPLIT readers
and the checksummed codec-0 and Snappy PLAIN V2 readers. The PLAIN laws
require that the footer declares tag 0, including for a zero-row group.
Pointwise successful group agreement composes to byte-identical IPC at
the same writer settings. The entry point uses the strict Snapshot
bounds and the existing annotation, framing, page, delta, lane, row,
file and IPC limits. Its scope is in-file flat required or optional
modern INT64 TIMESTAMP data with checked spans.

[Parquet 2.14.0 encoding rules](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Pinned Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift) ·
[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/ScalarDispatch/Thms.lean)

## Independent evidence

Twelve genuine PyArrow 26.0.1 files cover the three encodings with both
page versions and codecs. They include required local microseconds,
nullable UTC nanoseconds, an all-null group, and signed Int64 endpoints.
Thrift, zlib and independent scalar decoders check annotations, tags,
original offsets, extents, CRCs, masks and signed ticks. All twelve
Lean-emitted IPC streams match the homogeneous comparators byte for byte.

Two labeled within-chunk assemblies concatenate unchanged producer frames,
including headers and stored CRCs, under one codec per chunk. Both contain
all three tags and both page versions. A separate four-group assembly
relocates unchanged chunks and includes a mixed within-chunk group.
PyArrow independently reads all the assembled Parquet inputs and all
15 actual Lean-emitted IPC outputs. Six additional pinned controls and
separate limit and predecessor checks exercise ten typed refusals and
five complete earlier prefixes.

[Comparator](../../scripts/parquet-timestamp-scalar-dispatch-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-scalar-dispatch-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Thms \
  +Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs \
  +Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-scalar-dispatch-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-scalar-oracle
/tmp/parquet-timestamp-scalar-oracle/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-scalar-oracle/bin/python -I scripts/parquet-timestamp-scalar-dispatch-oracle/check.py
```
