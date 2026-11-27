# GZIP V1 dictionary Parquet TIMESTAMP to native Arrow IPC

`Timestamp.Leaf.Dictionary.Gzip.convert` selects one flat INT64 TIMESTAMP
leaf by its serialized footer ordinal. It admits modern TIMESTAMP
annotations and codec 2. Every selected chunk has one leading PLAIN
dictionary and RLE_DICTIONARY Data Page V1 frames. The reader checks the
original footer offsets and declared slot total before it expands the
dictionary. A PLAIN data page or a V2 data page is refused. The existing
TIMESTAMP entry points retain their admission policies.

Each frame uses its exact stored extent. A present Parquet page CRC-32
covers the complete stored GZIP payload. The decoder checks that the
whole payload is one GZIP member and verifies its distinct trailer CRC-32
and ISIZE against the expanded bytes. The dictionary yields the exact
declared number of signed PLAIN INT64 words. A V1 data member yields the
original flat required or optional level layout and a width-prefixed
hybrid reference stream. Reference lookups use that original chunk's
dictionary and preserve every signed nullable tick.

Dictionary entry, chunk, stored and expanded byte, level, row and file
caps remain in force. `Gzip.Limits.gzipCalls` defaults to 65,536 controller
calls per original member. This setting belongs to the opt-in converter.

The successful IPC law recovers the exact name, nullability, unit, and
UTC or local interpretation through EOS, with one batch per original
footer group. The first failed selected group retains its original cause
before writer admission. Events retain the earlier complete groups.
After framing, header and count admission, a data-page failure carries
its original page ordinal and absolute header offset. The dictionary
uses page ordinal zero.

## Independent readback

The pinned comparator generates genuine PyArrow 26.0.1 GZIP files for
nullable UTC nanos, required local micros, and nullable UTC millis with
the Parquet checksum absent. Thrift checks original metadata and
frame extents. zlib verifies the distinct page and member CRCs, the
member's exact extent, the expanded layout, and the signed values via
the independently observed dictionary indices. PyArrow reads the actual
Lean-emitted native Arrow V5 IPC through EOS.

Deterministic controls damage an outer CRC and separately damage the
dictionary or data member trailer while recomputing the outer CRC. A
two-fault file preserves the earlier indexed data error. The oracle also
checks the V2 and PLAIN fallback refusals and the byte, row, entry and
controller bounds.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Dictionary/Gzip/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-gzip-dictionary-v1-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-gzip-dictionary-v1-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-gzip-dictionary-v1-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-gzip-dictionary
/tmp/parquet-timestamp-gzip-dictionary/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-gzip-dictionary-v1-oracle/check.py
```
