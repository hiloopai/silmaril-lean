# Checked two-LIST Parquet writer

`Parquet.RecursiveSchema.TwoList.Writer.emit` accepts an Arrow declaration
with one named LIST of named LISTs over a named signed INT32 or INT64 leaf,
and an ordered list of logical Arrow batches. Each field may be optional
or required. The writer preserves names and nullability, the signed width,
and the distinction between null lists, empty lists, null leaves, and
present values.
[Logical row profile](parquet-recursive-two-list-rows.md)

Each batch becomes one row group with one unindexed UNCOMPRESSED PLAIN
Data Page V1. The page holds complete rows and starts with repetition zero
when it has slots. A zero-row batch produces a physical zero-slot page.
An empty batch list produces just the schema and footer. Page CRC is
optional and covers the original stored body when enabled. The Compact
footer contains the canonical LIST declarations, exact data offsets, and
each chunk's slot count and both header-inclusive totals. The writer
compiles its canonical schema with the existing Parquet reader to obtain
the original Dremel thresholds used for level serialization.

## Construction and checked readback

`serialize_construction` binds each serialized page to the canonical
row projection and signed words, the ordered page locations, and the
footer built from their actual lengths. Per-group row, slot, level, body,
header, and chunk limits complement file-wide group, row, slot, file,
and footer limits. Slot demand is measured before projecting the levels
and words. The writer measures both level sections and the signed suffix
before allocating the body.

`emit` exposes an output only after reopening its final bytes with the
existing checked Events reader. `emit_wire` includes the construction
witness and the separate checked readback witness. The readback recovers
the exact declaration, ordered batches and explicit row counts, and
terminates at EOS. It also yields `Rows.GroupWire` for each original
group. The event readback uses the same chunk and framing limits as
construction.
[Events profile](parquet-recursive-two-list-events.md)

The writer covers one physical page per group, one signed leaf and two
canonical LIST ancestors. Splitting groups into multiple pages,
additional codecs and encodings, indexes and pageless groups require
separate writer support. Struct-wrapped, multi-leaf and deeper LIST
shapes and nested projection are outside this profile.
[Reader codec and geometry matrix](parquet-recursive-two-list-dictionary-codecs.md)

## Verification

Pinned PyArrow reads 18 Lean-emitted files with all eight nullability
choices at both widths, signed extrema, multiple groups, schema-only
output, a physical empty group, and checksummed and checksum-free
pages. The independent oracle checks the Compact schema and footer, both
original totals, exact V1 frame extents, CRC, both Hybrid level sections,
and little-endian signed words in all 35 pages. Lean checks exact Rows
and full and empty Events through EOS. Twenty typed refusals cover
declaration and row errors, limits, and a checked readback mismatch.
[Producer and output pins](../../scripts/parquet-recursive-two-list-writer-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-writer-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-writer-oracle/check.py
~~~
