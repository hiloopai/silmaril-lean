# Snappy PLAIN Parquet TIMESTAMP to native Arrow IPC

Set `leaf.allowSnappy := true` in `Timestamp.Leaf.Events.ToIpc.Limits`
to admit codec 1 on the checked selected TIMESTAMP leaf. The default admits
only uncompressed chunks. The opt-in also admits uncompressed chunks, so
a selected leaf can have either admitted codec in a footer row group.
Other codec IDs remain outside the profile. Direct leaf and event reads use
the same `Timestamp.Leaf.Limits.allowSnappy` setting.

The physical profile is a flat required or optional INT64 leaf with PLAIN
V1/V2 data pages and the existing flat RLE level checks. The codec setting
is independent of annotation admission. A modern descriptor keeps its unit
and adjusted flag. Converted-only millis or micros requires the existing
`.allowConvertedOnly` annotation profile and retains its UTC interpretation.
The Arrow schema preserves the name, nullability, unit and UTC or local
descriptor. Signed ticks stay on their original epoch scale.

[Default TIMESTAMP IPC profile](parquet-timestamp-to-ipc.md) ·
[Converted-only annotations](parquet-converted-timestamp.md)

## Exact expansion and binding

- V1 passes the entire original page body to the bounded raw Snappy decoder.
  The checked scalar layer splits definition levels and PLAIN words from the
  exact expanded body.
- V2 leaves the definition prefix on disk. The checked scalar layer bounds
  that prefix against both sizes, subtracts it from both, and handles only
  the value suffix through the selected codec. A true `is_compressed` flag,
  including the wire default, uses Snappy. False uses exact raw values.
- The same snapshot and original header-derived parameters determine the
  byte spans, size validation, mask and reconstructed signed slots. The
  declared compressed and expanded page caps apply before decompression.
  Existing file, footer, page-count, level, group, row and sink limits
  remain in force.

`Leaf.readGroup_sound` binds the group observation to the original framed
chunk. `PhysicalFrame.preparedWire` exposes the exact V1/V2 preparation on
those same bytes, the checked mask and ordered signed PLAIN words.
`Events.readBound_reference` and `ToIpc.convertWith_readback` connect those
group observations to events and the complete IPC readback through EOS.
A late page error retains the original group and page indices and decoder
cause. Events retain earlier complete groups, and IPC emission returns the
source error before writer admission.

[Leaf and frame laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Thms.lean) ·
[Event laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/Thms.lean) ·
[IPC laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/ToIpc/Thms.lean) ·
[Existing scalar and Snappy decoder contract](parquet-scalar-page.md)

## Pinned interoperability

CPython 3.13.5, PyArrow 26.0.1 and Thrift 0.25.0 generate and check five
fixtures. PyArrow writes a modern UTC millis V1 file and two modern micros V2
files. A deterministic Compact Thrift footer edit yields the converted-only
UTC micros input with identical page bytes. The other V2 input remains
modern local. Every admitted file exercises signed Int64 endpoints, null
slots, multiple pages and an all-null group. The V2 files contain both
compressed value suffixes and raw bypass pages.

The oracle independently reads the Thrift frames and Snappy-covered slices,
checks the exact signed PLAIN words, and reads the actual Lean-emitted IPC
with PyArrow. Two mutations increase the raw Snappy output-size declaration
at group 2, page 1, leaving the original footer, frames and earlier groups
intact. Both readers refuse the corrupt group. Lean checks the exact
two-group event prefix, default codec and annotation refusals, and the
group, compressed-byte and expanded-byte limits.

[Producer and oracle](../../scripts/parquet-timestamp-snappy-oracle/check.py) ·
[SHA-256 pins](../../scripts/parquet-timestamp-snappy-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Tests +Silmaril.Formats.Parquet.Timestamp.Leaf.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-snappy
/tmp/parquet-timestamp-snappy/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-snappy/bin/python -I scripts/parquet-timestamp-snappy-oracle/check.py
```

## Optional stored CRC verification for PLAIN V2

`Timestamp.Leaf.SnappyV2.convert` selects the codec-1 flat INT64 PLAIN V2
profile explicitly. It uses the strict modern annotation binder. It admits
required and optional fields, preserves millis, micros and nanos, and emits
the original signed ticks with canonical UTC for adjusted timestamps and an
absent timezone for local timestamps. The existing PLAIN, dictionary and
mixed-profile entry points retain their admission policies.

The reader checks selected chunk spans and the group slot total before page
decoding. On each original frame it checks the stored size and verifies any
declared CRC-32 against the complete stored payload, including the raw
definition prefix. The scalar decoder then checks that prefix and the exact
value suffix. It uses Snappy for a compressed suffix and the raw value bytes
when the V2 flag is false. The proofs preserve frame order, original footer
group positions, null slots and signed counts through native Arrow V5 EOS.
The event trace retains complete earlier groups on a later error, and the
converter returns that source cause before attempting Arrow writer admission.
A CRC error includes the page ordinal and absolute header offset.

The pinned comparator reads genuine PyArrow inputs with Thrift and checks
both the stored CRC and the raw signed words independently. It covers all
three units, required and optional fields, UTC and local timestamps, Int64
endpoints, and both V2 value-suffix modes. Separate deterministic mutations
damage a level prefix, damage a value suffix, or refresh a stored CRC after
changing the Snappy size declaration. PyArrow independently checks refusal,
and Lean checks the exact earlier event batches and typed source precedence.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/SnappyV2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-snappy-v2-crc-oracle/check.py) ·
[SHA-256 pins](../../scripts/parquet-timestamp-snappy-v2-crc-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-v2-crc-oracle/Axioms.lean
/tmp/parquet-timestamp-snappy/bin/python -I scripts/parquet-timestamp-snappy-v2-crc-oracle/check.py
```
