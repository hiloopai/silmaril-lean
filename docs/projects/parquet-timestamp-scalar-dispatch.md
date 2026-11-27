# Selected dictionary-free Parquet TIMESTAMP scalar encodings

`Timestamp.Leaf.ScalarDispatch.convert` selects one modern flat INT64
TIMESTAMP leaf through the checked Snapshot. Each selected chunk can
use UNCOMPRESSED (codec 0), Snappy (codec 1), GZIP (codec 2), or
Zstandard (codec 6). Its footer encoding list
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

GZIP preparation uses the shared exact single-member path, including
the member trailer checks and a default controller allowance of 65,536
calls. Zstandard preparation uses the checked dictionary-free frame
decoder and its strict match-distance rule. This profile admits one
supported frame and bounds the window at 8 MiB and commands per block
at 43,690 by default. The output budget is the declared expanded
body or suffix length under the existing page cap. A literal V2
suffix consumes only its literal extent. [Checked Zstandard frame profile](zstd-huffman-frame.md)

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
and the checksummed PLAIN V2 readers for all four codecs. The GZIP and
Zstandard comparisons use equal controller and frame limits respectively.
The PLAIN laws require that the footer declares tag 0, including for a zero-row group.
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

The compressed comparison adds fourteen genuine PyArrow files. Twelve
cover GZIP and Zstandard across all three tags and both versions. Two
exercise required local microseconds. Native V2 files exercise both
storage flags. Thrift and zlib verify stored CRCs and GZIP members,
and libzstd 1.5.7 checks exact Zstandard frame extents. The three labeled
assemblies retain original producer frames and CRCs. Two mix tags and
page versions within a GZIP or Zstandard chunk. The six-group assembly
mixes all four codecs. PyArrow independently reads all 17 actual Lean
IPC outputs, including three byte-identical standalone PLAIN V2
comparisons. Late controls exercise outer CRC, GZIP trailer, Zstandard
magic, null-count and codec budgets, retaining the complete earlier
groups. Brotli supplies the unsupported-codec control in the original
comparator.

[Comparator](../../scripts/parquet-timestamp-scalar-dispatch-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-scalar-dispatch-oracle/fixtures.json) ·
[Compressed comparator](../../scripts/parquet-timestamp-scalar-codecs-oracle/check.py) ·
[Compressed fixture hashes](../../scripts/parquet-timestamp-scalar-codecs-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Thms \
  +Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs \
  +Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-scalar-dispatch-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-scalar-oracle
/tmp/parquet-timestamp-scalar-oracle/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-scalar-oracle/bin/python -I scripts/parquet-timestamp-scalar-dispatch-oracle/check.py
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-scalar-codecs-oracle/Axioms.lean
/tmp/parquet-timestamp-scalar-oracle/bin/python -I scripts/parquet-timestamp-scalar-codecs-oracle/check.py
```
