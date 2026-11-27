# GZIP V2 dictionary fallback for Parquet TIMESTAMP

`Timestamp.Leaf.Fallback.Gzip.V2.convert` selects one modern flat INT64
TIMESTAMP leaf by serialized ordinal. Every selected codec-2 chunk must
contain one leading PLAIN dictionary frame, a nonempty run of
RLE_DICTIONARY Data Page V2 frames, and a nonempty run of PLAIN Data Page
V2 frames. The checked footer offsets identify the dictionary and the
first data page. Frame planning checks this sequence and the group slot
total before decoding the dictionary or data. A dictionary-coded page
after the first PLAIN data page is rejected at its original ordinal and
header offset.

The dictionary body uses one bounded GZIP member. Each data page keeps its
raw definition-level prefix and has zero repetition bytes. The definition
extent fits both declared sizes. The header's storage flag selects a
single GZIP member or literal bytes for the value suffix, with sizes
checked after subtracting the level extent. A present Parquet CRC covers
the whole original stored payload, including raw levels, before decoding.
Each GZIP member verifies its own CRC-32 and ISIZE. The same preparation
and checksum checks cover both data phases.

The checked mask agrees with the V2 row and null counts. The prefix looks
up exact signed dictionary words in reference order. The suffix reads one
signed PLAIN word for each present slot. Native Arrow V5 IPC reads through
EOS with the original footer group boundaries, nullable signed ticks,
unit, field name and nullability. Adjusted timestamps use canonical UTC
and local timestamps have no timezone label. No tick rescaling takes place.
After successful planning and dictionary decoding, the first failed data
page retains its typed cause and original header offset. A failed footer
group preserves the earlier complete event batches and reaches IPC before
writer admission.

## Independent fixture evidence

PyArrow 26.0.1 produced both pinned positive files. Thrift observes
RLE_DICTIONARY, PLAIN, PLAIN in every group after its separate leading
dictionary. The nullable UTC nanosecond file exercises both storage flags
in both phases, page CRCs, distinct group dictionaries, nulls, repeated
ticks and the signed INT64 endpoints. The required local microsecond file
has no page CRCs or level bytes. zlib verifies the original CRC coverage,
exact member consumption and the member trailer. The comparator decodes
the raw masks, reference indices and signed words independently and uses
PyArrow to read the actual Lean IPC bytes through EOS.

Separate mutations cover CRC failures in both phases, corrupt GZIP
trailers with freshly computed stored CRCs, invalid raw references,
an incorrect raw PLAIN extent, reentry, missing phases, and faults
competing across pages or groups. Genuine V1 fallback and V2
dictionary-only controls exercise the strict profile boundaries.

[Public theorems](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Fallback/Gzip/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-gzip-fallback-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-gzip-fallback-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-gzip-fallback-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-gzip-fallback-v2-oracle/check.py
```
