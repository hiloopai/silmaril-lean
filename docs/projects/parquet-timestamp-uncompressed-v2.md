# Selected uncompressed PLAIN V2 Parquet TIMESTAMP

`Timestamp.Leaf.Uncompressed.V2.convert` opts into one checked modern
flat INT64 TIMESTAMP leaf with footer codec 0, no dictionary offset,
and PLAIN Data Page V2 frames. It uses the existing PLAIN chunk
selector with Snappy disabled and frames the exact original selected
span. The declared footer row total must match the ordered frame
slot counts before decoding.

Each V2 frame verifies a present CRC on the exact original stored
body before reading its parameters and values. The V2 header fixes
zero repetition bytes and the raw definition prefix. Its extent
fits both declared sizes. The shared decoder resolves a false flag
to codec 0 and a true flag to the footer codec. An absent flag
defaults to true. With footer codec 0, all three cases leave the
value suffix literal. The stored suffix and decoded bytes are
identical and account for both advertised lengths. A false flag
with unequal sizes fails original header admission. A true flag
with unequal codec-0 payload sizes fails the exact literal decoder.

The definition mask and exact signed little-endian PLAIN words
reconstruct nullable slots in original frame order. Page errors
retain their ordinal and a CRC failure includes its absolute header
offset. The first failed footer group retains the complete earlier
events and precedes writer admission. Native Arrow V5 IPC preserves
one batch per original group and the exact field name, nullability,
unit, UTC or local interpretation, and signed nullable ticks through
EOS.

## Independent evidence

Two genuine PyArrow 26.0.1 codec-0 files contain fifty original V2
pages, with nullable UTC nanoseconds and required local microseconds.
Both native files have explicit false storage flags. The UTC input
includes stored CRCs, nulls and signed endpoints. Thrift, zlib and
an independent hybrid decoder verify original frame extents,
raw definitions and exact signed words. PyArrow reads the selected
Parquet groups and four actual Lean-emitted IPC streams.

Separate Thrift mutations set the last UTC flag to true or remove it,
with the altered header length reflected in the footer sizes when
needed. The original payload and CRC bytes are preserved. Both
mutations produce byte-identical IPC to the native false-flag file.
Other controls check late original level and suffix CRCs, unequal
sizes under both flags, page encoding, declared rows, and a labeled
V1 assembly. The broader PLAIN reader admits the checksum-free V1/V2
assembly and emits identical IPC for the native checksum-free V2 file.
The Lean comparator checks eleven typed refusals and seven complete
earlier prefixes.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Uncompressed/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-uncompressed-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-uncompressed-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-uncompressed-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-uncompressed-v2-oracle/check.py
```
