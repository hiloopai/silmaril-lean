# Exact Parquet TIMESTAMP milliseconds to native Arrow seconds

`Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.convert` is the opt-in
inverse of the [seconds-to-millis writer](arrow-seconds-to-parquet.md).
It uses the strict modern PLAIN leaf reader at ordinal one and checks
that the original flat file contains one field in TIMESTAMP millis.
The input limits and PLAIN codec policy are those of the existing
reader. The output field keeps the original name and nullability.
An adjusted instant emits exact `UTC` and a local reading emits an
absent timezone.

The source opens under the ordinary file, group and row caps and every
original group read must succeed before rescaling. A source failure
keeps the existing indexed cause, including a late source failure
after earlier off-grid counts. After that checked read, the first
nonintegral count reports its original zero-based group, logical
slot, and signed millis value. The exact numeric inverse accepts a
count precisely when it is divisible by 1,000.

The native writer emits one Arrow V5 record batch per original group
and exact EOS. Explicit empty groups remain empty batches, and a
schema-only file emits zero batches. The strict reader continues to
require framed chunk spans. The default TIMESTAMP converter preserves
millis.

## Round-trip existence

`Existence.rescale_writer_image` derives complete inverse rescaling from
successful seconds-to-Parquet emission and matched intermediate Snapshot
and Leaf settings. The forward certificate checks the one-field shape
on the same retained readback binding. It supplies the checked groups,
millis descriptor, and exact original seconds observation. The theorem
recovers the entire original Arrow stream value, including explicit
empty groups, null slots, and local or UTC interpretation.

`Existence.roundtrip_exists` adds only the independent outer admission
conditions. `MiddleBounds` checks the file length, number of original
batches, and total rows against the inverse's file-level caps.
`SinkAdmits` describes the native Arrow serializer's own success and
normalized readback checks on the original Arrow stream. It can be
witnessed independently of the Parquet conversion. The inverse then
emits those exact bytes, and the Arrow reader recovers the original
seconds stream through EOS.

The sink comparator first serializes the original Arrow stream without
involving Parquet. PyArrow measures the metadata and body extents and
checks the source seconds observation. At those precise output limits,
the complete round trip emits the same certified bytes. Decreasing each
nonzero cap separately by one exercises typed refusals for schema or
record metadata, body bytes, fields, batches, per-batch rows, total rows,
and total cells. Empty and schema-only profiles exercise the exact zero
row and body limits.

[Existence theorems](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/ToIpc/Seconds/Existence/Thms.lean) ·
[Tight sink comparator](../../scripts/seconds-roundtrip-existence-oracle/check.py)

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/ToIpc/Seconds/Thms.lean) ·
[Default converter](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/ToIpc/Defs.lean)

## Pinned interoperability

PyArrow 26.0.1 writes independent PLAIN V1 UTC optional and PLAIN V2
local required files. They contain both convertible signed boundaries,
negative counts, and null and zero slots. Thrift verifies the original
millis annotation, adjusted flag and group counts. PyArrow independently
reads the actual Lean Arrow output and checks V5 framing through exact
EOS. Both positive and negative off-grid controls preserve an earlier
null in the offending group. The late source control changes the last
page's encoding tag in a genuine producer file while retaining its
original extent and body.

Four additional observations run the actual Lean seconds writer and
check the resulting Parquet bytes against the pinned writer image.
These cases cover consecutive empty groups, all-empty and schema-only
sources, required and nullable fields, and UTC and local interpretations.
The independent Arrow reader recovers the original second count lists
for all four.

[Comparator](../../scripts/parquet-millis-to-arrow-seconds-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-millis-to-arrow-seconds-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-millis-to-arrow-seconds-oracle/Axioms.lean
python3 -m venv /tmp/parquet-millis-to-arrow-seconds
/tmp/parquet-millis-to-arrow-seconds/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-millis-to-arrow-seconds/bin/python -I scripts/parquet-millis-to-arrow-seconds-oracle/check.py
```
