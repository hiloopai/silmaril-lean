# Opt-in selected Parquet DATE dictionary fallback

`Date.Leaf.Fallback.readAll` and `Date.Leaf.Fallback.toIpc` select one flat
DATE leaf by zero-based physical column ordinal. They reuse the strict
selected-leaf binding and the checked INT32 dictionary framer. The original
leaf annotation, path, name and required or optional repetition govern
every original chunk. A selected group uses its own leading PLAIN (0)
dictionary followed by a nonempty RLE_DICTIONARY (8) data prefix and a
nonempty PLAIN (0) data suffix. V1 and V2 data pages use the existing
uncompressed scalar and dictionary-index readers.
[DATE binding and annotation policy](parquet-date-selected-leaf.md)
· [Parquet 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md)

The phase check validates all data tags before decoding their bodies.
A PLAIN first data page, an all-dictionary group or a reference after
the switch is a typed group error. Framing retains the absolute
dictionary and first data offsets, checks the exact original page
extents, and enforces the existing uncompressed and CRC-rejecting
bounds. The strict PLAIN, dictionary-only and single-column page-less
entry points retain their admission rules. This profile's phase check
uses INT32 data pages and shares the checked chunk and both decoders
with the existing DATE paths.
[Executable profile](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Defs.lean)

`checkSequence_wire` witnesses the two nonempty phases.
`checkGroup_wire` attaches them to the retained chunk and its bounded
frames. `readGroup_wire` gives the ordered nullable signed slots and
the declared row count. `plainWire_exact` exposes the suffix validity
mask and exact PLAIN words. For the prefix, the dictionary page law
exposes the exact index stream and chunk-local lookups. The IPC law
recovers the descriptor, one batch per original footer group, and the
complete ordered DATE stream through exact EOS. The first-error laws
carry the original page failure to its original group index, retain
exactly the earlier complete event batches, and give the source failure
precedence over writer limits.
[Fallback theorem header](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Thms.lean)
· [Dictionary theorem header](../../Silmaril/Formats/Parquet/Date/Leaf/Dictionary/Thms.lean)

## Independent checks

PyArrow 26.0.1 emits genuine uncompressed V1 and V2 fallback files with
nullable DATE at physical ordinal 1 beside an unannotated INT32. The
producer uses the TIMESTAMP fallback oracle settings of an eight-byte
dictionary target, four-row write batches and a 24-byte data-page target.
For these INT32 fixtures each of the two groups has data cuts
`[4, 8, 8, 4]` and tags `[8, 0, 0, 0]`. Thrift 0.25.0 independently
checks the footer and absolute frame offsets. The oracle interprets levels,
dictionary references and signed PLAIN words and uses PyArrow to read the
same exact Date32 descriptor, signed endpoints, nullable slots, batches
and EOS from the Lean-emitted IPC.
[TIMESTAMP producer precedent](../../scripts/parquet-timestamp-fallback-oracle/check.py)
· [Arrow 26.0.1 source](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90)
· [Fixture fingerprints and observations](../../scripts/parquet-date-fallback-oracle/fixtures.json)

A Thrift edit truncates the final PLAIN word by one byte and adjusts
the page and chunk extents. PyArrow independently observes the prior
group and rejects the damaged one. Lean retains the earlier batch and
the original late group, page, offset and scalar cause even with a
zero output batch cap. Other controls cover PLAIN-first, dictionary
reentry, dictionary-only, PLAIN-only, compression and the independent
writer batch budget.
[Oracle](../../scripts/parquet-date-fallback-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Leaf.Fallback.Thms +Silmaril.Formats.Parquet.Date.Leaf.Fallback.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-fallback/Axioms.lean
python3 -I scripts/parquet-date-fallback-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
