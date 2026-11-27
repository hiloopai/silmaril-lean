# Selected TIMESTAMP dictionary V1 across four codecs

`Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.convert` opens
one checked modern flat INT64 TIMESTAMP leaf. Its dictionary-bearing
groups admit UNCOMPRESSED, Snappy, GZIP and bounded Zstandard data
pages of one version, V1 or V2. Each has one leading PLAIN dictionary
and RLE_DICTIONARY data. In the fallback profile, a nonempty run of
references precedes a nonempty PLAIN suffix. Dictionary-free groups
use the existing ScalarDispatch profile. The new entry point uses the
same limits as `WithV1.convert`.

The original footer column selects the codec and dictionary route.
A checked framing pass retains the original dictionary and data
offsets. The existing header classifier selects the data version and
uses the presence of PLAIN to choose the V1 phase policy. V2 continues
through the original dispatch strategies on the retained frame list.
The agreement laws include the prior typed V2 errors on classified
V2 chunks. The existing converters and strict standalone entry points
retain their admissions.

The two added V1 routes reuse the V2 PLAIN dictionary entry readers.
The original stored CRC and both declared extents are checked. Codec 0
uses the literal body. Zstandard uses one complete checked frame for
each dictionary and data page. There is no external Zstandard
dictionary. The route inherits the stored chunk, expanded chunk,
window, command and per-page budgets. V1 data preparation consumes the
whole stored body before splitting definition levels from the value
bytes. PLAIN words and bounded dictionary indices restore the
original nullable signed order under the selected UTC or local
descriptor. Successful native Arrow IPC reads through EOS with one
batch per original complete group.

An opposite data page version in a dictionary chunk is rejected at
its first original page ordinal and absolute offset. A dictionary
footer must contain tag 8 and may also list tags 0 and 3. Tag 2 and
scalar fallback tags remain outside the dictionary profile. A typed
source error stops at the first failed group and retains the complete
earlier Events before IPC writer admission.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/ScalarAndDictionary/WithV1/AllCodecs/Thms.lean) ·
[Prior Snappy/GZIP V1 profile](parquet-timestamp-dictionary-v1-groups.md) ·
[Pinned Parquet encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Pinned Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift) ·
[Zstandard frame format](https://www.rfc-editor.org/rfc/rfc8878)

## Independent evidence

Five genuine PyArrow 26.0.1 producers exercise the new V1 modes.
The inputs include nullable UTC nanoseconds, required local
microseconds, signed endpoints, repeated values and nulls. Independent
Thrift, CRC, Zstandard frame extent, mask, dictionary and signed word
checks bind their original bytes. Five additional native files
compare scalar and dictionary paths already served by `WithV1`.

A labeled nine-group assembly copies original chunks byte for byte,
relocating footer offsets. PyArrow independently reads the assembly
and all eleven actual Lean IPC streams. Five unchanged profiles
produce byte-identical predecessor IPC. The late controls include
competing stored CRC faults, leading dictionary CRC, an actual V1
tag-2 header, a labeled mixed-version chunk, and independently
chosen stored dictionary and expanded chunk limits. The comparator
checks the indexed error and complete earlier prefix under a zero
IPC batch budget.

[Comparator](../../scripts/parquet-timestamp-all-dictionary-v1-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-all-dictionary-v1-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-all-dictionary-v1-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-all-dictionary-v1
/tmp/parquet-timestamp-all-dictionary-v1/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-all-dictionary-v1/bin/python -I scripts/parquet-timestamp-all-dictionary-v1-oracle/check.py
```
