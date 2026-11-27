# Selected Snappy dictionary-backed Parquet DATE V2

`Parquet.Date.Leaf.Dictionary.Snappy.V2` opens one checked snapshot and
binds one flat INT32 DATE leaf by physical ordinal. The caller declares
`dictionaryOnly` or `fallback` for the selected groups. Both profiles
require one leading PLAIN Snappy dictionary and Data Page V2 headers
after it. Dictionary-only accepts a nonempty run of RLE_DICTIONARY pages.
Fallback requires a nonempty RLE_DICTIONARY prefix and a nonempty PLAIN
suffix. An earlier phase failure keeps its original coordinate ahead of
a subsequent unsupported header.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Snappy/V2/Defs.lean) ·
[Selected DATE binding](parquet-date-selected-leaf.md)

The profiles use the original selected chunk, offsets, frame chain and
stored CRC policy. The shared dictionary decoder expands the original
leading block to signed PLAIN entries. Each data page keeps the original
level bytes and a value suffix selected by the V2 compression flag.
The compressed suffix consumes one bounded Snappy block. The raw suffix
supplies the exact literal bytes. The data witnesses relate the checked
mask to signed PLAIN values or to the exact Hybrid indices and their
lookups. Typed body failures retain the existing Snappy cause and
page coordinate.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Snappy/V2/Thms.lean) ·
[Snappy PLAIN V2](parquet-date-snappy-plain-v2.md)

The event trace retains every complete footer group before the first
indexed failure. Native Date32 emission requires source EOS and preserves
the original name, nullability and footer-order signed slots through
exact IPC EOS. The explicit V2 profiles supply the dictionary-backed
prerequisites for per-group header-directed dispatch.

## Pinned comparison

Four genuine PyArrow 26.0.1 fixtures cover dictionary-only with and
without stored CRCs, and fallback with Snappy-compressed and literal
reference suffixes. The fallback inputs also cover both flags on PLAIN
pages. The comparator rechecks the pinned Thrift headers, zlib CRCs and
PyArrow decompression and independently decodes Hybrid indices before
comparing PyArrow's readback of Lean's IPC. The four IPC outputs match
the established Snappy readers byte for byte on these V2 inputs.

Genuine V1 and opposite-profile files exercise strict refusal. Labeled
mutations cover a damaged leading dictionary, an invalid reference
with valid CRC, a damaged late PLAIN page and illegal phase transitions.
The controls also check cumulative expansion and source precedence
over a zero IPC batch budget.
[Comparator](../../scripts/parquet-date-snappy-dictionary-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-snappy-dictionary-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true \
  tests/formats/parquet-date-snappy-dictionary-v2/Axioms.lean
python3 -I scripts/parquet-date-snappy-dictionary-v2-oracle/check.py
```
