# Opt-in raw Brotli in recursive signed Parquet dictionary chunks

The unindexed recursive signed INT32/INT64 Struct/LIST reader accepts
codec 4 with one leading PLAIN Parquet value dictionary when
`Rows.Limits.chunk.brotliRaw` is set. The same positional binding gate
applies to PLAIN and dictionary-first columns. With the default
`none`, codec 4 fails at the column binding even when all V2 data
suffixes have a false compression flag.
[Support matrix](parquet-recursive-dictionary-lz4-raw.md) · [Checked raw Brotli profile](parquet-recursive-brotli-raw.md)

The original column codec selects the bounded raw-meta-block adapter
for the leading dictionary, whole V1 data bodies and flagged V2
value suffixes. It checks the original stored-body CRC before
expansion and binds the exact stored and decoded extents to the
window and meta-block work caps. Entropy-coded and metadata
meta-blocks and trailing input are refused. Dictionary entry and
byte caps apply before publishing the ordered signed entries.

V2 reads the original raw repetition and definition spans. After
the dictionary is checked, a false flag uses the original raw
suffix with zero Brotli work. The original page encoding selects
exact Hybrid indices into the same column's ordered dictionary
or exact PLAIN signed words. The checked walk includes the
dictionary in the physical page budget and both header-inclusive
footer totals. V1 retains live List continuation across an encoding
change. V2 checks the row-start boundary, closes the cursor and
checks its null, slot and row counts. Writer and pageless admission
are unchanged.

## Fixtures and regressions

Pinned PyArrow quality-zero writes fully raw-profile dictionary-first
V1 and V2 with genuine PLAIN fallback. The genuine V2 files use
false-flag suffixes. A labeled V2 fixture wraps selected index and PLAIN
suffixes from an independently inspected uncompressed fallback file
in raw streams, keeping the original levels and selected bypasses.
A labeled V1 fixture carries a live row into PLAIN fallback. Genuine
quality-five controls reach entropy coding in a V1 data page and a
V2 leading dictionary.

Pinned libbrotli, independent raw meta-block inspection, Compact and
Hybrid checks account for original frames, CRCs, dictionary entries,
index traces, signed words and both footer totals. PyArrow reads the
Lean IPC output, and independent framing checks its exact EOS.
Typed controls cover dictionary and data CRC, entropy coding, excess
input, wrong extents, byte, window, work and page limits and footer
totals. Late dictionary CRC, trailing data and index failures retain
the completed group and original address through empty projection
and precede native IPC output limits.
[Producer, reference and fixture pins](../../scripts/parquet-recursive-dictionary-brotli-raw-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Thms +Silmaril.Formats.Parquet.ScalarPage.BrotliRaw.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-dictionary-brotli-raw-oracle/Axioms.lean
python3 scripts/parquet-recursive-dictionary-brotli-raw-oracle/check.py
~~~
