# Selected uncompressed dictionary-to-PLAIN V2 Parquet TIMESTAMP

`Timestamp.Leaf.Fallback.Uncompressed.V2.convert` reads one checked modern
flat required or optional INT64 TIMESTAMP leaf. Each selected codec-0 chunk
has a leading PLAIN dictionary, a nonempty RLE_DICTIONARY Data Page V2
prefix, and a nonempty PLAIN Data Page V2 suffix. The shared fallback
phase check refuses a return to dictionary references after the first
PLAIN page. It uses the original selected frame chain, footer offsets
and declared row count.

Each admitted dictionary or data body retains its exact original stored
span and verifies any present CRC. The dictionary is local to the chunk
and contains bounded literal signed PLAIN words. Each data page has zero
repetition bytes and a checked raw definition prefix. The reference and
PLAIN cases account for both declared sizes with the same literal suffix.
A false, true, or omitted V2 storage flag resolves to codec 0. A false
flag with unequal sizes fails header framing. A true flag with unequal
sizes fails the branch's literal payload extent check.

Framing, header planning, phase validation and the declared row total
precede data body decoding. During planning, the first failed header
retains its page ordinal and absolute header offset. After dictionary
admission, the first failed data frame retains its original ordinal,
absolute offset and typed checksum, reference or PLAIN cause. The first
failed group retains all complete earlier groups and precedes IPC writer
admission. Successful native Arrow V5 IPC retains the selected UTC or
local descriptor, signed nullable ticks and one batch per original group
through EOS. The existing broader V1/V2 reader retains its admission.

## Independent evidence

Two genuine PyArrow 26.0.1 codec-0 files have six native fallback groups,
each with data encodings `[8, 0, 0]`. They cover nullable UTC nanoseconds,
required local microseconds, and signed endpoints. Thrift, zlib and an
independent Hybrid reader check the original dictionary and continuation
offsets, exact literal extents, present CRCs, masks, reference lookups and
PLAIN words. PyArrow checks four actual Lean-emitted native streams.

Labeled header edits set a reference page's flag to true and omit a final
PLAIN page's flag in separate files. They preserve the original stored
bodies and CRCs and give byte-identical IPC to the false-flag producer.
The V1 and dictionary-only refusal files are labeled assemblies of genuine
chunks, with native readback checked independently. Retagged headers test
a PLAIN start and a return to references. Body and header mutations test
competing CRC faults, invalid reference width and unequal extents. The
comparison checks eighteen typed refusals and twelve complete prefixes.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Fallback/Uncompressed/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-uncompressed-fallback-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-uncompressed-fallback-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-uncompressed-fallback-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-uncompressed-fallback-v2-oracle/check.py
```
