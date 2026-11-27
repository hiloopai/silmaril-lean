# Mixed PLAIN V1 Parquet files with independent page cuts

`MixedV1Writer.MultiPage.emit order limits input` writes a bounded flat
Parquet file with one physical INT32 leaf and one opaque BYTE_ARRAY leaf.
Both field orders and required or optional fields are supported. Each
group supplies a list of typed PLAIN V1 pages for each column. The column
cuts may differ. The two complete slot lists must have the same length
and every page must match its declared field layout.

A nonempty group uses pages with positive slot counts in both columns. An empty
group uses exactly one zero-slot page per column. The file still contains
the group at that footer ordinal. An empty group list is refused.

The writer checks group, row, per-chunk page and aggregate page counts
before measuring pages. Measurements bound complete page bodies and chunk
extents before allocating page bodies. The Compact footer is limited by
its own budget and the file space remaining after the data and trailer.
The existing PLAIN BYTE_ARRAY encoder checks scalar and individual value
limits before allocating each scalar slice. Reader admission and framing
limits also apply independently.

Successful emission reparses the exact footer and every page header.
The first chunk starts at byte 4. Pages cover each chunk in ordinal
order, chunks and groups adjoin, and the final chunk ends where the
footer begins. `frame_at` gives an ordinal's absolute offset from the
preceding wire lengths. `column_size` equates a chunk's extent to the
sum of its header and payload lengths. `emit_indexed` recovers each
original group through the existing mixed reader. Unzipping the result
recovers both complete logical slot lists, so different cuts of the same
slots preserve positional pairing, nulls and present empty values.
[Theorems][laws]

The [oracle][oracle] checks two Lean-produced files with row groups
`[5, 0, 3]`, differing page counts per column and different cuts of the
same slots. PyArrow 26.0.1 checks the actual rows in either field order.
Thrift 0.25.0 checks every header and body, absolute first-page offsets,
chunk sizes and footer extent. Lean checks exact caps, fifteen typed
refusals, and byte equality with the original writer for singleton
page lists in both orders.

```sh
lake build --wfail +Silmaril.Formats.Parquet.MixedV1Writer.MultiPage.Checks
python3.13 scripts/parquet-mixed-v1-multipage-oracle/check.py --out /tmp/parquet-mixed-v1-multipage
```

[laws]: ../../Silmaril/Formats/Parquet/MixedV1Writer/MultiPage/Thms.lean
[oracle]: ../../scripts/parquet-mixed-v1-multipage-oracle/check.py
