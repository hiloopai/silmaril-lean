# Selected modern TIMESTAMP groups with Snappy and GZIP dictionary V1

`Timestamp.Leaf.ScalarAndDictionary.WithV1.convert` is a separate
opt-in reader for one checked modern flat INT64 TIMESTAMP leaf. It
uses the same input and output limits as `ScalarAndDictionary.convert`.

| Original selected column | Admitted data pages |
| --- | --- |
| No dictionary offset | Existing ScalarDispatch V1/V2 profiles across UNCOMPRESSED, Snappy, GZIP and Zstandard |
| Dictionary offset, Snappy or GZIP | A leading PLAIN dictionary followed by RLE_DICTIONARY pages of one version (V1 or V2). A nonempty PLAIN suffix may follow a nonempty reference prefix |
| Dictionary offset, UNCOMPRESSED or Zstandard | Existing strict V2 reference-only and one-way PLAIN fallback profiles |

The selected footer codec and dictionary offset determine the route.
For Snappy and GZIP dictionary groups, the reader frames the checked
original chunk once. The first original data version chooses the strict
version. A PLAIN data tag of that version chooses the fallback planner.
The selected planner and decoder use those retained frames and configured
limits. Their complete standalone results agree, including typed page
and codec failures. The existing V2 agreement also covers the full
result of the prior dispatchers on a classified V2 chunk.

The first other data version in that chunk is an unsupported layout with
its original data page ordinal and absolute header offset. This header
classification precedes the selected branch's plan and body checks.
Unsupported dictionary footer encoding lists and unknown codecs retain
the existing unsupported-profile error. Shared framing failures retain
the original cause under the existing codec arm because no version has
been selected yet. A classified V1 failure carries the exact error from
the corresponding V1 branch.

Tag 2, scalar fallback tags 5 and 9, a PLAIN-first dictionary chunk, a
return to dictionary references after PLAIN, and mixed dictionary data
versions within a chunk are outside this admission. The selected
dictionary-bearing footer still declares tag 8 and may include tags 0
and 3. Index metadata and external or malformed chunk extents remain
subject to the original selected-leaf and Snapshot checks.

The dictionary witness binds the original contiguous frame chain,
dictionary and data footer offsets, chunk cap, and original PLAIN
dictionary expansion. The data witnesses retain each original frame and
stored CRC check, the exact V1 header parameters, and decoder results
using those original bytes. The shared decoders verify exact V1
whole-body expansion, V2 raw levels and flag-selected value bytes,
dictionary indices or PLAIN words, and ordered nullable signed slots.
The GZIP witness includes the independent member checksum and exact
extent. Fallback has an explicit one-way phase witness. The trace
preserves every complete group before the first error. Successful IPC
readback through EOS preserves the selected field name, nullability,
unit, UTC or local interpretation, and each original group's ordered
signed nullable ticks.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/ScalarAndDictionary/WithV1/Thms.lean) ·
[Original scalar/dictionary profile](parquet-timestamp-scalar-dictionary.md) ·
[Pinned Parquet page encoding rules](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Pinned Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

## Independent verification

Five genuine PyArrow 26.0.1 V1 producers cover both modes and codecs
with nullable UTC nanoseconds, plus required local microseconds.
Independent Thrift and codec checks verify the stored CRCs, signed
dictionary entries, V1 definition masks, reference indices and PLAIN
suffix. Two native V2 dictionary files and a scalar file check predecessor
agreement. Each of the eight genuine files produced byte-identical
Lean IPC through its standalone or predecessor path.

The labeled seven-group assembly relocates only footer metadata and
copies scalar, V1 and V2 chunks byte for byte. PyArrow independently
reads each source group and all nine actual Lean IPC streams. The
controls check a V1 PLAIN CRC, a competing later dictionary CRC, a
dictionary footer tag-2 declaration, a strict chunk cap, and a labeled
assembly whose original V1 and V2 frames share an identical dictionary.
PyArrow independently reads the mixed-version control, and Lean reports
the first contrary header. All six refusals check the original typed
cause and complete earlier group prefix ahead of a zero IPC batch cap.

[Comparator](../../scripts/parquet-timestamp-dictionary-v1-groups-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-dictionary-v1-groups-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-dictionary-v1-groups-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-dictionary-v1-groups
/tmp/parquet-timestamp-dictionary-v1-groups/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-dictionary-v1-groups/bin/python -I scripts/parquet-timestamp-dictionary-v1-groups-oracle/check.py
```
