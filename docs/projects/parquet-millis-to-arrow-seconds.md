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

The composition theorem pairs successful seconds-to-Parquet and
Parquet-to-seconds calls. The two legs use the same intermediate
Snapshot and Leaf limits. Their other file, group, row and IPC caps
are independent and must admit the corresponding calls. The theorem
retains the certified intermediate file observation and recovers the
original Arrow descriptor, ordered nullable second counts, and batch
boundaries.

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
