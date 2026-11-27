# Selected scalar and dictionary Parquet TIMESTAMP groups

`Timestamp.Leaf.ScalarAndDictionary.convert` opens one checked modern
flat INT64 TIMESTAMP leaf. The original selected footer column supplies
a codec from UNCOMPRESSED, Snappy, GZIP and Zstandard. Its dictionary
offset determines which reader supplies that footer group.

| Original dictionary offset | Admitted selected chunk |
| --- | --- |
| Absent | ScalarDispatch with PLAIN, DELTA_BINARY_PACKED or BYTE_STREAM_SPLIT Data Page V1 or V2 |
| Present | One leading PLAIN dictionary followed by RLE_DICTIONARY V2 data, with the existing one-way PLAIN V2 fallback profile also admitted |

The dictionary-bearing footer must declare RLE_DICTIONARY (8), with
optional PLAIN (0) and RLE (3). Any listed DELTA_BINARY_PACKED (5),
BYTE_STREAM_SPLIT (9), deprecated PLAIN_DICTIONARY (2), or other tag
lies outside the dictionary route. Once selected, the existing
codec-specific dispatcher uses the original data frames to decide
between reference-only data and fallback. Fallback requires a nonempty
reference prefix followed by a nonempty PLAIN suffix. A reference after
the switch, dictionary-bearing V1 or mixed V1/V2 data, PLAIN-first
dictionary data, additional dictionary frames, and invalid offsets
remain outside those branch contracts. Dictionary-free V1 and V2
follow the full ScalarDispatch profile.

An unsupported codec or dictionary footer encoding list produces an
explicit profile error. After a supported route is selected, the
branch retains its own typed errors, including unsupported original
page headers, CRC mismatches and configured limit failures. There is
one branch call per group. The branch comparisons preserve its entire
result, including errors, and use its existing limits and original
frame witnesses.

The checked Snapshot supplies the original footer ordinals and chunk
bounds. Successful native Arrow V5 IPC preserves the selected name,
nullability, time unit, UTC or local interpretation, and one exact
signed nullable batch per original group through EOS. At the first
failed group the event trace retains the earlier complete batches,
and the converter returns the original indexed failure before IPC
writer admission. The route uses the strict Snapshot span policy for
in-file chunks.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/ScalarAndDictionary/Thms.lean) ·
[Dictionary-free scalar profile](parquet-timestamp-scalar-dispatch.md) ·
[Strict V2 dictionary dispatch limits](parquet-timestamp-mixed-codec-v2-uncompressed.md) ·
[Pinned Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

## Independent evidence

Eight genuine PyArrow 26.0.1 producers cover references and fallback
for all four codecs with nullable UTC nanoseconds. A ninth dictionary
file checks required local microseconds. Each has two original groups
with distinct dictionaries and signed endpoints. Thrift, zlib, libzstd
and independent mask and reference checks verify the original pages.
Three native scalar producers exercise DELTA_BINARY_PACKED V1,
BYTE_STREAM_SPLIT V2, and PLAIN V1.

The labeled eleven-group assembly copies original chunks byte for
byte and relocates their footer offsets. It interleaves scalar and
dictionary groups, with every dictionary codec and both data layouts.
PyArrow independently reads those groups and all 13 actual Lean IPC
streams. The twelve native files agree byte for byte with their
standalone Lean readers. The comparator checks 32 completed groups as
well as eight failures and their complete prefixes. The controls
include competing late CRCs, an advertised scalar tag union on a
dictionary-bearing group, an actual tag-9 dictionary-data header,
an unsupported codec, a genuine dictionary V1 chunk, and a strict
dictionary chunk cap.

[Comparator](../../scripts/parquet-timestamp-scalar-dictionary-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-scalar-dictionary-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-scalar-dictionary-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-scalar-dictionary
/tmp/parquet-timestamp-scalar-dictionary/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-scalar-dictionary/bin/python -I scripts/parquet-timestamp-scalar-dictionary-oracle/check.py
```
