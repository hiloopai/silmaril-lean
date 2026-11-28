# Bounded Zstandard in recursive signed Parquet dictionary chunks

The unindexed recursive signed INT32/INT64 Struct/LIST reader accepts
codec 6 with one leading PLAIN Parquet value dictionary. The codec
correspondence proof binds the decoder to the original column binding.
The original header selects RLE_DICTIONARY or PLAIN on each data page.
[Support matrix](parquet-recursive-dictionary-lz4-raw.md) · [Parquet codec IDs](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L670-L679)

The adapter checks one bounded Zstd frame with dictionary ID zero.
The Parquet value dictionary stores signed words for local page-index
lookup. It supplies no compression dictionary to Zstd. The existing
frame profile checks exact input and decoded extents, the window and
block walk, the configured sequence-command cap, and content size and
content checksum when present. Page CRC verification covers the
original stored body before expansion.
[Checked Zstd profile](parquet-recursive-zstd.md)

The leading dictionary and V1 data pages expand the entire original
body. V2 uses its original raw repetition and definition spans and
expands only the value suffix when the resolved flag is true. A false
flag bypasses the Zstd adapter entirely. Hybrid checks the exact
variable index extent and every lookup in the original ordered
dictionary. PLAIN pages check the exact signed-word extent.

The dictionary consumes one physical page in the budget and contributes
to both header-inclusive footer totals. Data pages retain exact slot
and row counts, V1 live List continuation, and V2 row-start and closure
checks. The same addressed failures propagate through Rows, direct
Events and native IPC. Writer and pageless admission are unchanged.

## Fixtures and regressions

Pinned PyArrow emits genuine codec-6 V1 and V2 files with RLE_DICTIONARY
and per-page PLAIN fallback. The V2 files cover compressed and raw
suffixes for both encodings. Labeled edits include raw bypass,
a V1 continuation into PLAIN, and Zstd content checksums on the
dictionary and both data-page versions. Independent libzstd, Compact
and Hybrid inspection checks original frames, CRCs, exact extents,
ordered entries, index traces and logical values. Raw IPC inspection
checks the emitted group counts through exact EOS.

Typed controls distinguish stored CRC and Zstd checksum errors and
exercise a nonzero compression dictionary ID, byte, window, sequence
and page caps, truncation, exact extents, a trailing byte and a second
complete frame. Late index and content checksum errors retain the
completed group and original page address through empty projection
and precede native IPC output limits.
[Producer, reference and fixture pins](../../scripts/parquet-recursive-dictionary-zstd-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-dictionary-zstd-oracle/Axioms.lean
python3 scripts/parquet-recursive-dictionary-zstd-oracle/check.py
~~~
