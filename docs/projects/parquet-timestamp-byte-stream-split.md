# Selected BYTE_STREAM_SPLIT Parquet TIMESTAMP

`Timestamp.Leaf.ByteStreamSplit.convert` selects one modern flat INT64
TIMESTAMP leaf. The selected column must advertise BYTE_STREAM_SPLIT
(tag 9), may advertise RLE levels, and must have no dictionary or index
page offset. The explicit route accepts footer codec 0 (UNCOMPRESSED) or
1 (Snappy). Each original data page must use tag 9, with its own checked
V1 or V2 header. Existing entry points retain their admission policies.

Selection associates the original row-group and leaf ordinals with the
footer's bounded chunk span. The reader checks the complete frame chain
and declared row total before page-body decoding. Each page checks its
stored length and any CRC on the original bytes. V1 uses the footer
codec on the entire body before splitting the level section. V2 keeps
the raw definition prefix, requires zero repetition bytes, and bounds
the prefix by both declared lengths. A true or absent storage flag
uses the footer codec on the exact value suffix. A false flag selects
literal bytes. Codec 0 leaves the suffix literal under either flag.

The Parquet 2.14.0 rules admit tag 9 for physical INT64. The prepared
value suffix contains exactly eight byte lanes of length equal to the
number of present slots, without padding. Byte `j` of present word `i`
comes from suffix offset `j * present + i`. The eight bytes implement
the original signed two's-complement little-endian word. The checked
definition mask restores nulls in original slot order.

The first failed footer group retains the complete earlier Events and
takes precedence over IPC writer admission. After framing and group
count admission, page failures retain the original page ordinal and
absolute header offset. Native Arrow V5 IPC preserves the selected name,
nullability, unit and UTC or local interpretation, with one batch per
original group and the exact nullable signed ticks through EOS.

[Parquet 2.14.0 encoding rules](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#byte-stream-split-byte_stream_split--9) ·
[Pinned Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift) ·
[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/ByteStreamSplit/Thms.lean)

## Independent evidence

PyArrow 26.0.1 produces eight genuine TIMESTAMP files across V1/V2,
UNCOMPRESSED/Snappy and nullable UTC nanoseconds/required local
microseconds. The fixtures include Int64 endpoints, distinct byte
patterns, nulls and zero, an all-null group, and both Snappy V2 flags
with nonempty suffixes. Thrift and zlib check the original annotation,
stored extents and CRCs. An independent deinterleaver compares the
signed words and levels with the PyArrow Parquet observations. PyArrow
also reads all eight actual Lean-emitted Arrow IPC streams through EOS.

Six labeled late-page mutations exercise CRCs, tags, V1 levels and a
truncated lane suffix. The truncation removes one byte from the final
page and repairs its declared sizes and the footer totals. Two other
genuine inputs exercise PLAIN and GZIP refusal. Additional controls
check frame, stored byte, expanded byte and scalar byte budgets, and
the default PLAIN entry point's tag-9 refusal.

[Comparator](../../scripts/parquet-timestamp-byte-stream-split-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-byte-stream-split-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.ByteStreamSplit.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-byte-stream-split-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-bss
/tmp/parquet-timestamp-bss/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-bss/bin/python -I scripts/parquet-timestamp-byte-stream-split-oracle/check.py
```
