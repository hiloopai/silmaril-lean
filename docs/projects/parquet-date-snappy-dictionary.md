# Opt-in selected Snappy Parquet DATE dictionaries

`Date.Leaf.Dictionary.Snappy.readAll` and
`Date.Leaf.Dictionary.Snappy.toIpc` select one required or optional flat
INT32 DATE leaf by zero-based physical column ordinal. The strict selected
leaf binding supplies the original raw annotation, path and descriptor.
Each selected chunk uses Parquet codec 1 (Snappy), one leading PLAIN (0)
dictionary and RLE_DICTIONARY (8) V1 or V2 data pages. A PLAIN data page
is an indexed encoding error. This profile covers dictionary-only chunks.
[DATE binding and annotation policy](parquet-date-selected-leaf.md)
· [Parquet 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md)
· [Pinned Parquet IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

The original framed range must match the selected footer group and
chunk and be disjoint from its neighbors. The compressed span and
sum of original expanded page sizes have separate chunk limits.
Dictionary entry count, page octets, scalar expansion, levels and
indices have their respective bounds. A stored CRC is optional.
When present it is checked over the original stored payload before
expansion or index decoding. V1 expands the whole body. V2 checks the
stored body including its raw levels, then decodes only the value
suffix with the codec selected by the original compression flag.
[Executable profile](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Snappy/Defs.lean)

`stored_verified` gives the original bounded byte slice and its CRC
when present. `readEntries_wire` ties the exact bounded Snappy
expansion to its signed PLAIN dictionary words. `checkGroup_wire`
retains the original frame chain, first data offset, dictionary offset
and declared slots. `pageWire_exact` exposes the exact prepared
validity mask and Hybrid indices and their in-range lookups.
`toIpc_readback` relates the result to the original descriptor and
signed nullable slots, with one native Date32 batch per footer group
through exact EOS. The first-error laws retain the earlier complete
batches and return the original indexed error ahead of writer limits.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Snappy/Thms.lean)

## Independent checks

PyArrow 26.0.1 writes the three pinned variants, V1 with CRC and V2
with and without CRC. The optional DATE field follows an unannotated
INT32 and covers nulls, repeated dates and both signed Int32 endpoints.
The V2 fixtures exercise both values of the on-wire compression flag.
Apache Thrift 0.25.0 reads the raw metadata and frame headers.
The comparator checks stored CRCs with zlib, expands with PyArrow
Snappy, and independently reads the masks, packed indices and signed
PLAIN words. PyArrow reads the actual Lean-emitted Date32 IPC.
[Pinned Arrow source](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90)
· [Fixture fingerprints and observations](../../scripts/parquet-date-snappy-dictionary-oracle/fixtures.json)

Separate late mutations exercise CRC failure in the stored dictionary
and data bodies, and an out-of-range index after recomputing its stored
CRC. PyArrow checks the earlier prefix and rejects each damaged group.
Other controls exercise dictionary, data and aggregate expansion limits
and refusal of a genuine Snappy PLAIN fallback. The strict PLAIN,
uncompressed dictionary and uncompressed fallback entry points reject
the Snappy files under their original codec policies.
[Oracle](../../scripts/parquet-date-snappy-dictionary-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms +Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-snappy-dictionary/Axioms.lean
python3 -I scripts/parquet-date-snappy-dictionary-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
