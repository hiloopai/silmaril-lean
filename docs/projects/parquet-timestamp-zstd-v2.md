# Selected PLAIN V2 Parquet TIMESTAMP with Zstandard

`Timestamp.Leaf.Zstd.V2.convert` opts into codec 6 PLAIN Data Page V2
on one required or optional modern flat INT64 TIMESTAMP leaf. The
existing leaf binder selects the chunk by original footer group and
serialized schema ordinal. The reader checks its codec, singleton path,
physical type, disjoint span, and declared row count. It bounds stored
chunk bytes and the sum of the pages' declared expanded bytes before
decoding. Per-page byte and level limits apply independently.

Each present Parquet CRC covers the entire original stored body. The V2
header selects the exact raw definition-level prefix, with zero
repetition bytes. After the definition extent is checked against both
sizes, a false compression flag selects a literal value suffix. A true
flag, including the parser's default for an absent flag, selects one
bounded dictionary-free Zstandard frame. The raw mask agrees with the
header's null count, and exact PLAIN signed words fill the original
present slots in order. The adapter shares the checked scalar
preparation used by the DATE reader.

Native Arrow V5 readback through EOS preserves each original group
boundary, nullable signed count, tick unit, field name and nullability.
The selected adjusted descriptor maps to canonical UTC and the local
descriptor has an absent timezone. Group failures retain earlier
complete batches in the event trace and reach the converter before
writer admission. Once framing, group byte bounds and slot totals are
admitted, the first page failure retains its original ordinal, absolute
header offset and typed cause.

## Zstandard profile

This path inherits the checked Huffman frame decoder's supported
dictionary-free block modes and strict match-distance rule
`distance < Window_Size`. It rejects skippable frames, nonzero
dictionary IDs, trailing bytes and concatenated frames. A frame content
checksum, when present, is verified separately from the Parquet CRC.
The adapter defaults to a maximum window of 8 MiB and 43,690 commands
per block. The value suffix's exact expected output size supplies the
output budget. A literal suffix requires no Zstandard window or command
budget. [Checked Zstandard frame profile](zstd-huffman-frame.md) ·
[DATE V2 scalar path](parquet-date-zstd-v2.md)

## Independent evidence

Three genuine PyArrow 26.0.1 files cover nullable UTC nanos with Parquet
CRCs, required local micros without Parquet CRCs, and nullable local
millis with raw suffixes only. They include nulls and signed INT64
endpoints. The raw-only case includes an all-null page with an empty
value suffix and runs with zero window and command budgets. Thrift
identifies the actual chunk spans and page headers, zlib verifies stored
CRC coverage, and libzstd 1.5.7 checks the original exact frame extent.
PyArrow reads both the original slot sequence and the actual
Lean-emitted Arrow IPC.

Separately labeled rewrites exercise stale CRCs, invalid frame magic
with a recomputed stored CRC, both incorrect flag directions, invalid
levels and null counts, and two competing failed groups. Genuine V1,
dictionary, and Snappy controls exercise the strict profile boundaries.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Zstd/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-zstd-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-zstd-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-zstd-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-zstd-v2-oracle/check.py
```
