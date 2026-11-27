# Selected dictionary-only V2 Parquet DATE with Zstandard

`Parquet.Date.Leaf.Dictionary.Zstd.V2` binds a single physical flat
INT32 DATE ordinal in the original checked snapshot. It checks codec 6,
the actual dictionary and data offsets, and the original frame order.
One leading PLAIN dictionary is followed by a nonempty sequence of
RLE_DICTIONARY Data Page V2 frames. The header plan rejects other
page versions and encodings at their original page offset. Stored and
expanded chunk bounds are checked independently. Existing strict
PLAIN and default readers keep their admission.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Zstd/V2/Defs.lean) ·
[Selected DATE binding](parquet-date-selected-leaf.md)

For each frame the reader verifies any present Parquet CRC on the
whole original stored payload before expanding it. The dictionary
body is one bounded dictionary-free Zstandard frame. Its exact
regenerated extent supplies the declared number of signed PLAIN
Int32 entries in original order. Data pages keep the raw definition
levels. The resolved V2 flag selects the exact raw index suffix or
one bounded Zstandard frame. The shared width-prefixed Hybrid reader
consumes the exact reference stream and checks every index against
the original dictionary. The ordered nullable slots agree with the
V2 counts and the footer row count.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Zstd/V2/Thms.lean) ·
[Selected PLAIN V2 DATE](parquet-date-zstd-v2.md) ·
[Flat INT32 Zstandard](parquet-flat-zstd.md)

Native Date32 IPC retains the selected field name and nullability and
one signed nullable batch per footer group through EOS. The event
trace retains the complete earlier groups and the first typed source
error. That error precedes IPC writer limits.

## Pinned comparison

Three genuine PyArrow 26.0.1 files use level 3 Zstandard and have six
original dictionaries and 18 reference pages. They cover nullable and
required DATE, both signed Int32 endpoints, stored CRCs present and
absent, and both native V2 storage flags. Thrift checks codec and
header fields and original absolute spans. Libzstd 1.5.7 checks frame
extents, zlib checks stored CRCs, and the independent Hybrid runner
checks the raw mask and reference order. PyArrow reads the producer
files and the Lean-emitted Date32 IPC independently.

Typed controls distinguish genuine V1 and fallback refusals from
edited headers, bad stored CRCs, invalid Zstandard magic and trailing
input with repaired CRC, a corrupted reference with repaired CRC,
and lower caps. The late controls preserve the earlier group with
the writer limited to zero batches.
[Comparator](../../scripts/parquet-date-zstd-dictionary-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-zstd-dictionary-v2-oracle/fixtures.json) ·
[libzstd 1.5.7](https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-zstd-dictionary-v2/Axioms.lean
python3 -I scripts/parquet-date-zstd-dictionary-v2-oracle/check.py
```
