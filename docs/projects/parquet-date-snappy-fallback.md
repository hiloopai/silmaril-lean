# Opt-in selected Snappy Parquet DATE fallback

`Date.Leaf.Fallback.Snappy.readAll` and
`Date.Leaf.Fallback.Snappy.toIpc` select one flat required or optional
INT32 DATE leaf by zero-based physical ordinal. They reuse the strict
selected-leaf binding and the Snappy DATE dictionary framer. Every
selected chunk has codec 1 (Snappy), a leading PLAIN dictionary, a
nonempty RLE_DICTIONARY data prefix and a nonempty PLAIN data suffix.
The existing DATE fallback rule checks the phase transition.
[Selected DATE binding](parquet-date-selected-leaf.md)
· [Snappy DATE dictionary framing](parquet-date-snappy-dictionary.md)
· [Parquet 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md)

After framing, header planning retains the prefix before the first
unsupported header. A phase error in that prefix takes priority over
the subsequent unsupported header. A missing end-of-sequence condition
lets the actual indexed header error through. The data-page ordinal
starts at one after the leading dictionary, and the error retains its
absolute header offset. Whole-chunk framing errors retain the shared
framer's typed cause. The dictionary-only API uses its original
RLE_DICTIONARY-only data planner.
[Phase and error contracts](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Snappy/Thms.lean)

Per-chunk expanded size includes the dictionary and both data phases.
The declared data slot counts add across both phases and must equal the
original group count of rows. Every data body has its original stored
extent checked before decode and a stored CRC is verified when present.
The V1 decoder expands the whole stored payload. V2 verifies the
whole stored payload including levels, then uses the original flag to
decode the value suffix. The dictionary branch retains its exact mask
and chunk-local index lookups. The PLAIN branch retains its exact mask
and signed PLAIN words. Successful Date32 IPC exhausts the source and
preserves the field name, nullability and every ordered nullable signed
slot, with one batch per footer group through exact EOS. The first
late failure forwards the original typed cause before writer limits and
retains exactly the earlier complete batches in the event trace.
[Executable profile](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Snappy/Defs.lean)
· [Dictionary payload contracts](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Snappy/Thms.lean)

## Independent checks

PyArrow 26.0.1 emits genuine CRC-bearing V1 and V2 fallback files with
two groups and tags `[8, 0, 0, 0]` in each selected chunk. The fixtures
adapt the TIMESTAMP oracle's page settings to signed INT32. Two
V2 fixtures cover both stored compression-flag values in both data
branches. The optional DATE follows an unannotated INT32 and includes
negative days, nulls, repeats and signed endpoints. Apache Thrift
0.25.0 reads the original frame headers, zlib verifies stored CRCs,
and the oracle decodes masks, references and signed words independently.
PyArrow reads the emitted Date32 IPC with exact batches. Lean also
emits at the pinned inclusive expanded-chunk cap.
[TIMESTAMP fixture precedent](../../scripts/parquet-timestamp-snappy-fallback-oracle/check.py)
· [Pinned Arrow source](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90)
· [Fixture fingerprints and observations](../../scripts/parquet-date-snappy-fallback-oracle/fixtures.json)

The malformed controls are separate from the genuine outputs.
Stored-byte flips exercise CRC errors in a V1 PLAIN payload, the V2
raw level prefix of a PLAIN page, and a V2 dictionary-coded data
payload. Thrift header edits exercise wrong first phase, both orders
of reverse-transition versus unsupported-tag priority, and a late
cumulative row-count mismatch. Budget controls cover aggregate
expansion and an individual PLAIN page. The pinned genuine
dictionary-only source exercises the missing PLAIN suffix.
[Oracle](../../scripts/parquet-date-snappy-fallback-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Thms +Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-snappy-fallback/Axioms.lean
python3 -I scripts/parquet-date-snappy-fallback-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
