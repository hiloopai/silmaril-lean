# Selected DELTA_BINARY_PACKED Parquet TIMESTAMP

`Timestamp.Leaf.Delta.convert` reads one checked modern flat INT64
TIMESTAMP leaf. The selected column must use footer codec 0 (UNCOMPRESSED)
or 1 (Snappy), advertise DELTA_BINARY_PACKED (tag 5), and have no dictionary
or index page offset. The footer can also advertise RLE levels. Each data
page independently supplies its original V1 or V2 header and tag 5. This
entry point accepts either codec directly. The existing PLAIN, dictionary,
fallback, and mixed-codec entry points retain their admission policies.

The checked Snapshot associates the selected path and original column span
with each footer row group. Framing and the declared group slot sum are
checked before page-body decoding. Each admitted frame checks its stored
extent and any CRC before preparing the body. V1 expands the exact whole
body under the footer codec before splitting levels. V2 keeps its raw
definition-level prefix, requires zero repetition bytes, and checks the
prefix against both sizes. The suffix uses the footer codec when the flag
is true or absent, and is literal when false. For codec 0 the suffix is
literal under either flag.

The decoder consumes the exact bounded delta stream for the number of
present slots and reconstructs nullable slots in wire order. As specified
by the pinned Parquet encoding rules, additions reconstruct signed
INT64 modulo 2^64, including overflow at either signed endpoint. The
reader preserves footer order and the exact earlier complete groups on
the first failed group. After framing admission, page-body failures retain
the original page ordinal and absolute header offset. Source failures
are returned before native Arrow writer admission. Successful output has
one V5 record batch per group, with the selected name, nullability, unit,
UTC or local interpretation, and exact signed nullable ticks through EOS.

[Parquet format 2.14.0 DELTA_BINARY_PACKED rules](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#delta-encoding-delta_binary_packed--5) ·
[Pinned page headers](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift) ·
[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Delta/Thms.lean)

## Independent evidence

Eight genuine PyArrow 26.0.1 files cover the cross product of V1/V2,
UNCOMPRESSED/Snappy, and nullable UTC nanoseconds/required local
microseconds. They exercise both signed endpoints, wrap in both directions,
null versus zero, an all-null group, several pages per group and both
Snappy V2 flags. Thrift and zlib check original annotations, offsets,
sizes, and stored CRCs. An independent parser checks level masks, the
exact delta stream extent, and signed reconstruction. PyArrow independently
reads the input groups and all nine actual Lean IPC outputs through EOS.

The mixed-version and mixed-codec four-group file is a labeled assembly
of unchanged producer chunks with relocated footer offsets. The comparator
checks the copied bytes and independently reads the assembled file. Six
labeled mutations check late CRC, encoding and delta geometry faults with
complete earlier groups. Two additional native files provide PLAIN and
GZIP refusals. Budget controls test frame count, stored and expanded bytes,
and packed bytes.

[Comparator](../../scripts/parquet-timestamp-delta-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-delta-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-delta-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-delta
/tmp/parquet-timestamp-delta/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-delta/bin/python -I scripts/parquet-timestamp-delta-oracle/check.py
```
