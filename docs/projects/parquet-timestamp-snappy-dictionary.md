# Snappy dictionary Parquet TIMESTAMP to native Arrow IPC

`Timestamp.Leaf.Dictionary.Snappy.convert` explicitly selects the
dictionary-only Snappy profile for one flat required or optional INT64
TIMESTAMP leaf. It takes the serialized schema ordinal with the root at
zero. The selected column chunk in each footer group must declare codec 1,
start with one PLAIN dictionary page, and continue with RLE_DICTIONARY V1
or V2 data pages. Each group uses its own dictionary. A PLAIN fallback page
is refused. The uncompressed dictionary and fallback APIs and the PLAIN
converter retain their existing admission policies.

The annotation profile is independent of compression. An admitted modern
descriptor retains its unit and adjusted flag. A converted-only descriptor
uses the existing explicit UTC admission. Native IPC preserves the original
name, nullability, unit, signed counts and UTC or local interpretation.

[Uncompressed dictionary profile](parquet-timestamp-dictionary.md) ·
[Uncompressed fallback profile](parquet-timestamp-fallback.md) ·
[PLAIN Snappy profile](parquet-timestamp-snappy.md)

## Stored payload and expanded bytes

The shared checked selector retains the original snapshot, chunk,
dictionary and data offsets. Framing and planning check the original page
order and declared slot count. Every stored payload passes its advertised
extent and byte limit before it is read by a decoder. A present CRC-32
covers the entire original on-disk body. The status for an absent CRC
still requires the exact stored extent.

- The dictionary uses the original checked PLAIN header and Snappy
  expansion of its whole stored body. The smaller of the dictionary and
  page caps applies independently to the stored and expanded lengths.
  The entry cap applies before expansion. The expanded body must contain
  exactly the declared PLAIN signed INT64 words.
- A V1 data page expands the whole body before the scalar reader separates
  the optional definition levels and index stream.
- A V2 data page keeps its raw definition prefix. The scalar reader bounds
  it by both declared sizes, then uses the resolved compression flag.
  True, including an omitted flag, selects Snappy for the value suffix.
  False selects exact raw indices. The CRC still covers both regions of
  the original stored body.

The wire laws give the exact source slice and CRC relation, bounded
Snappy expansion, original header parameters, mask and index bytes,
and ordered signed dictionary lookups. Group observations match the
declared slot totals. The event and IPC laws preserve the complete groups
in footer order. After planning, the first decode failure retains its
group, wire page ordinal, original absolute header offset and typed cause.
The dictionary has wire ordinal zero. Events retain prior complete groups,
and conversion returns the source error before the IPC writer runs.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Dictionary/Snappy/Thms.lean) ·
[Stored page CRC contract](parquet-page-crc32.md) ·
[Scalar page compression](parquet-scalar-page.md)

## Pinned interoperability

CPython 3.13.5, PyArrow 26.0.1 and Thrift 0.25.0 reproduce eight fixtures.
The successful Parquet files are modern UTC nanos V1, modern local micros
V2, and converted-only UTC micros V2. PyArrow writes all data and dictionary
pages. A deterministic Thrift footer edit supplies the converted-only
annotation over the same UTC page bytes. The files include repeated signed
ticks, nulls, distinct dictionaries, and both signed Int64 endpoints.
V2 contains actual compressed value suffixes and raw bypass pages.

The oracle reads absolute frame extents with Thrift, verifies stored CRCs
using zlib, expands Snappy with PyArrow, independently checks masks and
dictionary indices, and reads the actual Lean-emitted Arrow V5 streams.
The late controls mutate a dictionary's stored Snappy length, a V2 raw
definition prefix, and a checksum-free V2 Snappy suffix size. They check
the original indexed causes, the exact two-group event prefix, and source
error precedence over sink admission.

[Oracle](../../scripts/parquet-timestamp-snappy-dictionary-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-snappy-dictionary-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-dictionary-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-snappy-dictionary
/tmp/parquet-timestamp-snappy-dictionary/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-snappy-dictionary/bin/python -I scripts/parquet-timestamp-snappy-dictionary-oracle/check.py
```

## Deprecated V1 dictionary tags

`Timestamp.Leaf.Dictionary.Snappy.LegacyV1.convert` explicitly admits the
parquet-java `PARQUET_1_0` profile for one modern flat INT64 TIMESTAMP
leaf. Each selected codec-1 chunk has a leading dictionary page tagged
`PLAIN_DICTIONARY` (2), followed by V1 data pages with the same tag. The
dictionary stores ordinary signed PLAIN words and the data uses the same
bounded hybrid reference decoder as tag 8. The existing dictionary-only
and fallback entry points retain their admission policies.

The profile uses the checked snapshot and original footer offsets. It
normalizes `BIT_PACKED` (4) to RLE only where the corresponding maximum
level is zero and the level stream is absent. An optional definition
stream still requires RLE. The stored checksum covers the complete
original payload. Snappy expands the whole body within the admitted
length before separating V1 levels from references.

The file and group laws recover one ordered native Arrow V5 batch per
footer group through EOS. The original descriptor, signed ticks and null
positions are exact. After successful page planning, the first failed
page retains its original ordinal, absolute header offset and cause.
A late source failure preserves earlier complete events and takes
precedence over IPC writer admission.

Two unmodified parquet-java 1.16.0 files cover nullable local micros and
required UTC nanos, chunk-local dictionaries, multiple groups, signed
Int64 endpoints and checksummed V1 data. Thrift, zlib and PyArrow
independently check the page headers, stored CRCs, expanded levels,
reference indices and native IPC. The oracle also constructs three
controls that preserve frame extents. They damage a stored CRC, introduce
an out-of-range reference after a null with a recomputed CRC, and put a
BIT_PACKED tag on an optional definition stream. The first two mutations
are independently refused by PyArrow.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Dictionary/Snappy/LegacyV1/Thms.lean) ·
[parquet-java producer](../../scripts/parquet-timestamp-snappy-legacy-dictionary-oracle/Write.java) ·
[Comparator](../../scripts/parquet-timestamp-snappy-legacy-dictionary-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-snappy-legacy-dictionary-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-legacy-dictionary-oracle/Axioms.lean
/tmp/parquet-timestamp-snappy-dictionary/bin/python -I scripts/parquet-timestamp-snappy-legacy-dictionary-oracle/check.py

fixture_tmp=$(mktemp -d)
mvn -B -q -f scripts/parquet-dictionary-chunk/pom.xml \
  org.apache.maven.plugins:maven-dependency-plugin:3.8.1:build-classpath \
  -Dmdep.outputFile="$fixture_tmp/classpath"
java -cp "$(cat "$fixture_tmp/classpath")" \
  scripts/parquet-timestamp-snappy-legacy-dictionary-oracle/Write.java "$fixture_tmp"
sha256sum "$fixture_tmp"/*.parquet
```
