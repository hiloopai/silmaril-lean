# GZIP V1 dictionary-to-PLAIN Parquet TIMESTAMP to native Arrow IPC

`Timestamp.Leaf.Fallback.Gzip.convert` is an opt-in converter for modern
flat required or optional INT64 TIMESTAMP. Each selected codec-2 chunk has
one leading PLAIN dictionary, a nonempty run of RLE_DICTIONARY V1 data
pages, and a nonempty PLAIN V1 suffix. The original selected frames and
footer offsets witness that one-way transition. The current PLAIN,
dictionary-only, Snappy, and uncompressed readers retain their policies.

The reader checks the original frame sequence and declared slot total
before decoding bodies. A stored Parquet CRC, when present, covers the
complete original on-disk payload. Each dictionary or data payload expands
as one bounded GZIP member with its own CRC-32 and ISIZE trailer. The original
V1 level prefix supplies the nullable mask. Its value region gives the
ordered dictionary indices or the exact signed PLAIN words. The converter
uses the dictionary profile's existing byte, entry, level, row, and
per-member controller budgets.

The native Arrow V5 readback preserves the field name, nullability, unit,
UTC or local interpretation, and every signed count through EOS. Each footer
group yields one batch in order. A late source error preserves the completed
earlier groups and preempts IPC writer admission. After successful group
planning, the first failed data page keeps its original wire ordinal,
absolute header offset, and typed cause.

## Independent producer and readback

PyArrow 26.0.1 writes the three pinned GZIP V1 files directly. They cover
nullable UTC nanos, nullable local micros, and required local millis with
the Parquet CRC absent. Each selected chunk has an original `8, 0, 0` data
sequence. Thrift and zlib independently check the original headers, frame
extents, both checksum layers, masks, references, and PLAIN signed counts.
PyArrow reads the actual Lean-emitted streams through EOS.

The mutated controls damage either a stored payload CRC or a GZIP member
CRC with the outer CRC recomputed. Other mutations remove either phase or
return to dictionary encoding after the first PLAIN page. The reentry
control also damages the preceding PLAIN CRC to exercise planning
precedence. A separate two-fault payload control verifies that the first
data decoding error wins after successful planning.

[Dictionary-only GZIP profile](parquet-timestamp-gzip-dictionary-v1.md) ·
[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Fallback/Gzip/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-gzip-fallback-v1-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-gzip-fallback-v1-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-gzip-fallback-v1-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-gzip-fallback-v1-oracle/check.py
```
