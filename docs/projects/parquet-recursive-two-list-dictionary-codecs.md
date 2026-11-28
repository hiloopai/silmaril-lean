# Checked dictionary codec parity for two-LIST Parquet

The reader accepts unindexed V1 and V2 for one signed INT32 or INT64
leaf under two canonical LISTs. Each row group binds its original column
codec and its own leading PLAIN dictionary when declared. PLAIN and
RLE_DICTIONARY data pages use the same codec selection in that chunk.

| Codec | Parquet ID | Payload profile |
| --- | ---: | --- |
| UNCOMPRESSED | 0 | Exact raw bytes |
| SNAPPY | 1 | One exact raw Snappy block |
| GZIP | 2 | One bounded RFC 1952 member |
| ZSTD | 6 | One bounded dictionary-free frame in the existing checked profile |
| LZ4_RAW | 7 | One exact raw LZ4 block |

The checked Zstd profile uses compression dictionary ID zero. The
original Parquet value dictionary is a separate table of signed words.
The same shared decoder and bounds apply to the leading dictionary,
whole V1 bodies and flagged V2 suffixes. The stored page CRC is checked
over the original frame. GZIP's member CRC and ISIZE and optional Zstd
content checksums are checked by their payload readers.
[Checked payload profiles and bounds](parquet-recursive-two-list-codecs.md)

The original dictionary offset and first data offset bind consecutive
frames. Both footer totals include the original dictionary header and
body. Each present slot consumes one exact Hybrid index into the local
dictionary. V2 keeps the raw repetition and definition spans and
uses the original raw index or PLAIN suffix under a false flag.
V1 keeps its live cursor across encoding changes. V2 closes the row
boundary. Direct Events retains every complete earlier group and the
original error under empty projection. IPC checks the source before
output admission.
[Dictionary wire model](parquet-recursive-two-list-dictionary.md) · [Events](parquet-recursive-two-list-events.md)

## Reproduction

Pinned PyArrow generates genuine dictionary-only and fallback V1/V2
chunks for LZ4_RAW, GZIP and Zstd at both signed widths across the
fixture matrix. Independent Compact, Hybrid, liblz4, zlib and libzstd
inspection checks the original dictionary entries, index traces, PLAIN
tails, stored CRC and header-inclusive totals. The mixed-codec file
copies original serialized frames of five genuine row groups. The oracle
checks Lean's native IPC through exact EOS.

Labeled edits inspect false-flag V2 index suffixes. The GZIP and Zstd
cases exercise zero codec work on the suffix after checking the leading
dictionary. Typed late failures preserve the original addressed source
error under both selections and ahead of exhausted IPC output limits.
The mixed Zstd control rejects an index that exists in an earlier LZ4
dictionary and lies outside the local table.
[Producer, source and IPC pins](../../scripts/parquet-recursive-two-list-dictionary-codecs-oracle/fixtures.json)

## Remaining structural gaps

- Schema compilation covers exactly one top-level LIST of LISTs and one
  unannotated signed leaf. Struct-wrapped two-LIST fields, repeated
  siblings, multi-leaf row reconstruction, and deeper LIST ancestry
  remain outside the native reader. The LIST-path core compiles longer
  canonical signed paths and checks their logical traces.
  [LIST-path core](parquet-recursive-list-path.md)
- Framing covers positive-sized unindexed chunks. Column and offset
  indexes and explicit pageless two-LIST groups remain separate geometry.
  A schema-only source has no row groups to read.
- Projection selects the one complete top-level field or the empty
  schema. Nested projection remains a separate capability. The checked
  writer emits the initial unindexed UNCOMPRESSED PLAIN V1 profile.
  [Two-LIST writer profile](parquet-recursive-two-list-writer.md)
- The encoding matrix covers PLAIN and RLE_DICTIONARY. Legacy
  PLAIN_DICTIONARY and other value encodings remain outside it. Opt-in
  raw-meta-block Brotli is a separate codec profile.

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-dictionary-codecs-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-dictionary-codecs-oracle/check.py
~~~
