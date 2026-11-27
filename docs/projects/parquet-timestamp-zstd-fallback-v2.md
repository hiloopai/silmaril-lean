# Selected Zstandard V2 Parquet TIMESTAMP dictionary fallback

`Timestamp.Leaf.Fallback.Zstd.V2.convert` opts into one required or
optional modern flat INT64 TIMESTAMP leaf with codec 6. Each selected
chunk has one leading PLAIN dictionary frame and a nonempty
RLE_DICTIONARY Data Page V2 prefix followed by a nonempty PLAIN Data
Page V2 suffix. The original footer determines the selected chunk,
dictionary offset and first data offset. The original frame chain
determines each phase, and every page after the first PLAIN page is
PLAIN.

The shared group admission applies the stored chunk cap, the sum of
the declared expanded dictionary and data bodies, the phase check and
the original row total before expanding the dictionary. The decoder
then uses the strict dictionary reader for the prefix and the strict
PLAIN reader for the suffix. Each admitted frame verifies a present
Parquet CRC across the full original stored body before decoding. The
dictionary consumes one bounded Zstandard frame and exact signed
INT64 words.

The V2 definition prefix remains raw, and repetition bytes are zero.
The original storage flag chooses a literal suffix or one exact
bounded Zstandard frame in each phase. The definition extent fits
both sizes, and the decoded mask agrees with the declared null count.
Reference pages look up signed words in the original chunk-local
dictionary. PLAIN pages read signed words directly. Both reconstruct
the original nullable slot order.

Compressed suffixes and the leading dictionary use the checked
dictionary-free Zstandard frame profile, with match distances below
the declared window size and default limits of an 8 MiB window and
43,690 commands per block. The frame content checksum is verified when
present. [Frame profile](zstd-huffman-frame.md) ·
[Dictionary-only V2](parquet-timestamp-zstd-dictionary-v2.md) ·
[PLAIN V2](parquet-timestamp-zstd-v2.md)

Native Arrow V5 IPC reads through EOS with one batch per original
footer group, preserving its field name, nullability, unit, exact
signed counts, and UTC or local descriptor. The first source group
failure retains the complete earlier event batches and precedes writer
admission. Framing, phase and row admission occur before body
decoding. A header or data-page failure keeps its original ordinal,
absolute header offset, and typed cause.

## Independent evidence

Two genuine PyArrow 26.0.1 files contain six original dictionaries and
18 data pages. Each original data sequence is RLE_DICTIONARY, PLAIN,
PLAIN. Both files exercise both storage flags in both phases. The
nullable UTC nanosecond file has stored CRCs, nulls and signed INT64
endpoints. The required local microsecond file has zero definition
bytes and absent stored CRCs. Thrift, zlib and libzstd 1.5.7
independently verify the frame boundaries, flags, CRCs and exact
frame extents. PyArrow reads the actual Lean-emitted IPC.

Separately labeled mutations exercise CRCs and bad frame magic in
each phase, incorrect flags, an invalid reference width, row preflight,
reentry, and competing failures across pages and groups. Genuine V1,
PLAIN-only and dictionary-only files exercise the narrow profile
boundaries.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Fallback/Zstd/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-zstd-fallback-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-zstd-fallback-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-zstd-fallback-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-zstd-fallback-v2-oracle/check.py
```
