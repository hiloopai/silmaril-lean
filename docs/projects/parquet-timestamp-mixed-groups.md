# Mixed-group Parquet TIMESTAMP to Arrow IPC

`Timestamp.Leaf.MixedGroups.convert` binds one flat required or optional
INT64 TIMESTAMP leaf at its serialized schema ordinal, with the root at
zero. Every footer group contributes one explicit Arrow V5 batch, in
footer order. The annotation profile applies once to the selected leaf.
The stream preserves the field name, nullability, unit, UTC or local
interpretation, signed ticks, and null positions.

The mixed entry point admits codecs 0 and 1 independently in each group.
The original selected column's dictionary offset chooses the PLAIN or
dictionary planner. The original checked page headers then determine the
page sequence.

| Planner | Admitted sequence |
| --- | --- |
| PLAIN | V1 or V2 PLAIN data with the existing codec and metadata rules |
| Dictionary only | One leading PLAIN dictionary frame and a nonempty RLE_DICTIONARY run |
| Dictionary fallback | One leading PLAIN dictionary frame, a nonempty RLE_DICTIONARY run, and a nonempty PLAIN suffix |

Dictionary scopes end at the selected chunk. The shared selectors keep
the exact footer group, column path, physical type, disjoint extent,
original dictionary and data offsets, and declared row count. The
dictionary and fallback planners share one framing and header pass and
reuse the existing codec and body checks. The PLAIN path checks the
original frame list and parameters, then uses the existing PLAIN
decoder for the framed bytes. The selected branch runs once. Its V1
whole-body and V2 definition-prefix and value-suffix rules are those of
the existing decoders. Stored CRC admission also comes from those
decoders.

Unknown codecs return the original codec ID. Unknown page kinds or
encoding tags fail the corresponding planner. A return to references
after fallback returns the original page ordinal and header offset.
The strict snapshot reports a page-interval error for a zero-byte
page-less chunk before group dispatch. A schema-only file has no chunks
to classify and can emit an empty stream. The narrow converters retain
their existing admissions.

Framing, header admission, and declared counts are checked before group
body decoding. After a plan succeeds, decoding stops at the first
failing data page. Event collection retains exactly the earlier
complete footer groups and the typed error of the first failing group.
Conversion reports that source error before Arrow writer admission.
Successful output reads back to the selected descriptor and exact
footer-order nullable counts.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/MixedGroups/Thms.lean) ·
[Snappy fallback profile](parquet-timestamp-snappy-fallback.md) ·
[PLAIN Snappy profile](parquet-timestamp-snappy.md)

## Pinned interoperability

The comparator assembles separate PyArrow 26.0.1 one-group files into a
UTC nanos file and a local micros file. It copies the column chunks
unchanged and uses Thrift to relocate footer offsets and assemble the
group list. Both assembled files contain all six codec and page-sequence
combinations, with V1 and V2 pages and a distinct decoy column. Thrift
independently checks exact frame extents, codec IDs, and data tags.
PyArrow reads the assembled Parquet files and the actual Lean-emitted
Arrow IPC streams with batch lengths `[4, 6, 4, 4, 768, 768]`, signed
extrema, and exact EOS.

Pinned controls include a native PyArrow schema-only file, a native
page-less file, and edits to the assembled local file for an unsupported
codec, an unsupported page tag, a return to dictionary encoding after
fallback, and a bad late Snappy CRC. All indexed failure checks compare
the complete earlier events with independent expected ticks.

[Oracle](../../scripts/parquet-timestamp-mixed-groups-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-mixed-groups-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-mixed-groups-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-mixed-groups
/tmp/parquet-timestamp-mixed-groups/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-mixed-groups/bin/python -I scripts/parquet-timestamp-mixed-groups-oracle/check.py
```
