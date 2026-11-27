# Page-less groups in mixed Parquet TIMESTAMP streams

`Timestamp.Leaf.MixedGroups.PageLess.convert` is an opt-in reader for
a flat Parquet TIMESTAMP leaf with PyArrow-style no-frame groups.
It binds the original schema ordinal and annotation once. Every
admitted no-frame group contributes one explicit zero-row Arrow V5
batch in its original footer position. A schema-only file emits a
Schema and EOS with zero batches.

The profile checks two kinds of evidence before admitting a no-frame
group.

- The original footer declares zero rows, zero values for every
  column, and zero stored and expanded sizes. Group and chunk offsets
  use the zero sentinel, with no dictionary, index, bloom filter,
  or external column fields. The columns match the original ordered
  flat schema. Each empty column has the producer's RLE-only encoding
  list and codec 0 or 1.
- The raw Compact row group and chunk fields match the no-frame
  convention, including an empty encoding-stats list. The framed
  chunks pass ordinary footer validation and form a packed cover of
  the data region in footer group and column order. A no-frame group
  takes no slice and leaves the physical cursor unchanged.

The checked Snapshot retains the original bytes, footer, and group
ordinals. The regular Snapshot constructor keeps the strict
positive-span rule. A zero-row group with an actual dictionary
frame and a zero data-page sentinel is outside this profile.
The profile supports Parquet version 2 flat files in the packed
layout above.

Framed groups run the existing mixed reader on the same source and
ordinal. The disjointness guard excludes only groups checked by the
opt-in constructor as occupying no bytes. The original selected
descriptor, signed nullable slots, and first indexed group failure
are preserved. The emitted IPC stream retains every complete batch,
including consecutive empty batches, in footer order.

[Footer witness and refusal laws](../../Silmaril/Formats/Parquet/Footer/PageLessTimestamp/Thms.lean) ·
[Event and IPC laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/MixedGroups/PageLess/Thms.lean) ·
[Mixed TIMESTAMP profiles](parquet-timestamp-mixed-groups.md)

## Pinned interoperability

Native PyArrow 26.0.1 files cover uncompressed UTC nanos V1 and
Snappy local micros V2 with empty groups before and between
nonempty groups, consecutive empty groups, an all-empty file, and
a schema-only file. Thrift checks the raw no-frame metadata fields.
PyArrow independently reads each Parquet source and the actual
Lean-emitted IPC, including the exact number and order of empty
batches.

The heterogeneous control inserts a producer-native empty group
entry into the assembled mixed group's footer. The column chunk
bytes and offsets are identical to the mixed input. A corresponding
late CRC mutation preserves the exact six earlier batches, including
the empty batch, and retains the original checked page offset.
Additional controls cover a native dictionary frame in a zero-row
group, missing pages for positive counts, zero rows with nonzero
column values, an incorrect empty column path, nonempty raw encoding
stats, and an unclaimed byte before the footer.

[Comparator](../../scripts/parquet-timestamp-page-less-oracle/check.py) ·
[Pinned fixture hashes](../../scripts/parquet-timestamp-page-less-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-page-less-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-page-less
/tmp/parquet-timestamp-page-less/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-page-less/bin/python -I scripts/parquet-timestamp-page-less-oracle/check.py
```
