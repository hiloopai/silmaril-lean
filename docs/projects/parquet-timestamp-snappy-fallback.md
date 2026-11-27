# Snappy fallback Parquet TIMESTAMP to native Arrow IPC

`Timestamp.Leaf.Fallback.Snappy.convert` selects a flat required or optional
INT64 TIMESTAMP leaf by its serialized schema ordinal, with the root at zero.
Each selected chunk must declare codec 1 and contain one leading PLAIN
dictionary frame, a nonempty run of RLE_DICTIONARY data pages, and a nonempty
PLAIN data suffix. Each chunk has its own dictionary. Both data segments may
use V1 or V2. The PLAIN, dictionary-only, and uncompressed fallback entry
points keep their existing admission rules.

The existing annotation profile selects modern TIMESTAMP or explicitly
admits a converted-only UTC descriptor. The stream preserves the selected
name, nullability, unit, and UTC or local interpretation, with one explicit
batch per footer group. Signed ticks and null positions are exact.

## Stored bytes and page order

The checked chunk binds the selected leaf and footer group to the original
dictionary and data offsets. The frame chain covers the original bounded
chunk. Planning checks the segment order and declared row total before
decoding bodies. A present CRC-32 covers the complete original stored body.
The absent-CRC case still checks the original body extent and stored byte
cap. The PLAIN dictionary expansion checks the entry cap and both stored
and expanded byte limits.

- V1 expands the entire body before the checked scalar reader separates
  definition levels from indices or PLAIN values.
- V2 uses the original raw definition prefix, with its length checked
  against both declared sizes. The header compression flag chooses Snappy
  or exact raw bytes for the value suffix. CRC verification covers both
  regions before either is consumed.

The page laws relate ordered signed slots to the original frame and checked
V1 or V2 preparation. After planning succeeds, the first failed data
decoder returns its original typed cause with its wire page ordinal and
absolute header offset. The dictionary has ordinal zero. Event collection
retains all earlier complete footer groups and carries the failing group
index. Conversion returns that source error before IPC writer admission.
Successful native IPC readback recovers the exact descriptor and ordered
nullable counts.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Fallback/Snappy/Thms.lean) ·
[Snappy dictionary-only profile](parquet-timestamp-snappy-dictionary.md) ·
[Uncompressed fallback profile](parquet-timestamp-fallback.md)

## Pinned interoperability

PyArrow 26.0.1 directly writes modern UTC nanos V1 and modern local micros
V2, each with two groups of 768 nullable signed ticks and independent
dictionaries. Every selected chunk has one PLAIN dictionary frame and
three data pages with encoding tags `8, 0, 0`. V2 includes both Snappy and
raw PLAIN suffix pages. The converted-only UTC micros V2 control uses a
deterministic Thrift footer edit over original PyArrow-produced pages.

The comparator pins all nine input files. It uses Thrift for original
frame extents and encodings, zlib for stored CRCs, PyArrow for Snappy
expansion, and independent level, index and signed-word checks. PyArrow
reads the actual Lean-emitted Arrow V5 schema, batches and exact EOS.
Late controls cover a dictionary CRC, V1 PLAIN CRC, V2 raw definition
prefix CRC, and a checksum-free V2 PLAIN Snappy size error. They compare
the entire earlier group and the original indexed failure.

[Oracle](../../scripts/parquet-timestamp-snappy-fallback-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-snappy-fallback-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-fallback-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-snappy-fallback
/tmp/parquet-timestamp-snappy-fallback/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-snappy-fallback/bin/python -I scripts/parquet-timestamp-snappy-fallback-oracle/check.py
```

## Snappy V1 fallback with deprecated dictionary tags

`Timestamp.Leaf.Fallback.Snappy.LegacyV1.convert` selects a modern flat
INT64 TIMESTAMP leaf in an original parquet-java `PARQUET_1_0` file.
Each selected codec-1 chunk contains one leading tag-2 dictionary, a
nonempty run of tag-2 V1 data pages, and a nonempty suffix of tag-0 PLAIN
V1 data pages. The checked phase witness connects this split to the
original frame order and declared slot total. The existing modern
fallback and legacy dictionary-only entry points retain their policies.

The legacy V1 planner preserves the original frame and scalar encoding.
It normalizes a BIT_PACKED level tag only for an absent section at maximum
level zero. An optional definition-level stream uses RLE. CRC verification
covers the exact original stored body. Bounded Snappy expansion supplies
the full V1 body to the existing level and reference or PLAIN decoder.
All successful output slots retain their exact signed counts.

The frame and event laws preserve the complete earlier groups and carry
the first selected group error before IPC writer admission. Within a group,
frame and phase planning precede body decoding. Successful planning then
allows the first failed data-page decode to retain its original ordinal,
absolute header offset and typed cause. Native IPC readback through EOS
preserves the original descriptor and one batch per footer group.

The pinned fixture is unmodified parquet-java 1.16.0 output. Both footer
groups contain a nullable local micros leaf and a required UTC nanos leaf,
with separate dictionaries and five tag-2 data pages before five PLAIN
pages per leaf. Thrift, zlib and PyArrow check the stored spans, CRCs,
definition masks and signed values independently. PyArrow also checks
both Lean-emitted IPC streams. Deterministic controls corrupt a later
dictionary or PLAIN payload, remove either phase, or return to tag 2
after the first PLAIN page. A damaged unselected leaf leaves the other
leaf's complete IPC output intact.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Fallback/Snappy/LegacyV1/Thms.lean) ·
[parquet-java producer](../../scripts/parquet-timestamp-snappy-legacy-fallback-oracle/Write.java) ·
[Comparator](../../scripts/parquet-timestamp-snappy-legacy-fallback-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-snappy-legacy-fallback-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.LegacyV1.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-legacy-fallback-oracle/Axioms.lean
/tmp/parquet-timestamp-snappy-fallback/bin/python -I scripts/parquet-timestamp-snappy-legacy-fallback-oracle/check.py

fixture_tmp=$(mktemp -d)
mvn -B -q -f scripts/parquet-dictionary-chunk/pom.xml \
  org.apache.maven.plugins:maven-dependency-plugin:3.8.1:build-classpath \
  -Dmdep.outputFile="$fixture_tmp/classpath"
java -cp "$(cat "$fixture_tmp/classpath")" \
  scripts/parquet-timestamp-snappy-legacy-fallback-oracle/Write.java "$fixture_tmp"
sha256sum "$fixture_tmp/fallback.parquet"
```
