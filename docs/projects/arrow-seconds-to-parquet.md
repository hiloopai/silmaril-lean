# Exact Arrow TIMESTAMP seconds to Parquet milliseconds

`Parquet.Timestamp.FromIpc.Seconds.convert` opts into conversion of
one flat little-endian Arrow V5 TIMESTAMP seconds field to canonical
Parquet INT64 TIMESTAMP millis. The original field name and nullability
are retained. The timezone must be absent for local readings or exactly
`UTC` for adjusted instants. An explicit empty string, offset label, or
other timezone returns a typed refusal.

The input byte cap applies before the original Arrow reader. The reader
checks the original Schema, all original batches, and exact EOS before
metadata admission, rescaling, or any sink work. An original read failure
keeps its indexed cause. Successfully read sources then use the existing
fixed-point signed-payload conversion. Each present slot becomes its
exact seconds count times 1,000. The inclusive convertible range is
`[-9223372036854775, 9223372036854775]` seconds. Either overflow returns
the original zero-based batch and logical slot, counting preceding nulls.

The existing writer and its readback certification produce one
uncompressed PLAIN V1 group per original explicit batch. The seconds
certificate also checks that the retained footer has exactly the root
and the written leaf. Empty batches
remain explicit groups and a schema-only stream produces zero groups.
The writer's strict entry point continues to refuse seconds. Successful
readback preserves exact nanosecond denotation under the original epoch
interpretation, and the exact inverse recovers the original second
counts with their nullable batch shape.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/FromIpc/Seconds/Thms.lean) ·
[Canonical writer](../../Silmaril/Formats/Parquet/Timestamp/FromIpc/Defs.lean)

## Pinned interoperability

PyArrow 26.0.1 produces the UTC optional and local required Arrow inputs,
along with all-empty and schema-only cases. The checker uses Thrift and
PyArrow to verify the actual Lean-emitted annotation, adjusted flag,
legacy millis tag, field, page extents, and raw signed INT64 counts.
It independently derives the signed bounds, checks null versus zero,
and recovers the original seconds by exact integer division.

The 14 pinned source cases include both boundary overflows, wrong unit,
and named, offset, and present-empty timezone refusals. The present-empty
label is a deliberate FlatBuffers edit. Truncation, missing EOS, and
trailing-byte cases mutate genuine PyArrow streams with an earlier
overflow. A missing-EOS case on an unsupported timezone also verifies
that the original wire error wins.

[Comparator](../../scripts/arrow-seconds-to-parquet-oracle/check.py) ·
[Fixture hashes](../../scripts/arrow-seconds-to-parquet-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-seconds-to-parquet-oracle/Axioms.lean
python3 -m venv /tmp/arrow-seconds-to-parquet
/tmp/arrow-seconds-to-parquet/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/arrow-seconds-to-parquet/bin/python -I scripts/arrow-seconds-to-parquet-oracle/check.py
```
