# Selected uncompressed dictionary-only V2 Parquet TIMESTAMP

`Timestamp.Leaf.Dictionary.Uncompressed.V2.convert` reads one modern flat
required or optional INT64 TIMESTAMP leaf. The selected chunk uses footer
codec 0 and has one leading PLAIN dictionary and at least one RLE_DICTIONARY
Data Page V2. The shared dictionary selector admits the original checked
chunk, verifies its dictionary and first-data offsets, and checks the
complete declared row total. A V1 data header is refused as an unsupported
page. A PLAIN continuation is refused at its own page ordinal and absolute
header offset. The existing codec-0 dictionary and fallback readers retain
their V1/V2 policies.

The dictionary is local to the chunk. Its original stored span and any
present CRC are checked before decoding its bounded literal PLAIN words.
Each admitted data page checks its original stored span and CRC before
reading the level and index streams. The level prefix is raw, with zero
repetition bytes and a checked definition mask. The remainder is a literal,
width-prefixed Hybrid reference stream with exact stored and declared
uncompressed extents. The V2 flag may be true, false, or absent. All three
resolve to codec 0. A false flag with unequal sizes fails header framing,
and a true flag with unequal sizes fails the literal payload extent check.

Successful pages resolve ordered references against the same dictionary,
reconstruct nullable signed slots and retain the selected unit and UTC or
local interpretation. The first failed header is returned in planning order.
After successful planning and dictionary admission, the first failed data
body is returned in page order. The event trace retains all complete groups
before the first failed group. The converter reports that cause before IPC
writer admission. Successful native Arrow V5 IPC preserves the selected
field descriptor, exact ticks and one batch per footer group through EOS.

## Independent evidence

Two genuine PyArrow 26.0.1 producers supply six distinct dictionaries and
fifty original reference pages, covering nullable UTC nanoseconds and
required local microseconds with repeated negative ticks and signed
endpoints. Thrift, zlib and an independent Hybrid decoder check original
offsets, PLAIN words, masks, index extents, lookups and present CRCs.
PyArrow reads all four actual Lean-produced streams.

Separately labeled header edits set the final V2 storage flag to true or
omit it, preserving the stored body and CRC. Those two files produce
byte-identical IPC to the original false-flag file. A labeled assembly
appends a genuine V1 dictionary chunk after two V2 groups. Another genuine
producer contains a V2 dictionary-to-PLAIN transition. The strict reader
refuses both at the original continuation frame, while the applicable
broader readers still accept them. Other controls cover a bad dictionary
CRC, a late raw-level CRC, an out-of-range literal reference, unequal sizes
under both flag values, and byte and entry caps.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Dictionary/Uncompressed/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-uncompressed-dictionary-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-uncompressed-dictionary-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-uncompressed-dictionary-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-uncompressed-dictionary-v2-oracle/check.py
```
