# GZIP V2 dictionary Parquet TIMESTAMP to native Arrow IPC

`Timestamp.Leaf.Dictionary.Gzip.V2.convert` explicitly selects a modern
flat INT64 TIMESTAMP leaf. Each selected codec-2 chunk has one leading
PLAIN dictionary frame and only RLE_DICTIONARY Data Page V2 frames. The
dictionary still uses one bounded whole-body GZIP member. The existing
V1, Snappy, and uncompressed entry points retain their admission policies.

An original V2 data body contains its exact raw definition-level prefix
and stored reference suffix. The flat profile requires zero repetition
bytes. The definition extent fits the stored and expanded sizes, and its
mask matches the header's row and null counts. The parsed compression
flag selects one exact GZIP member for the suffix or literal stored
reference bytes. A present Parquet CRC covers the entire original body,
including the raw levels. A compressed suffix also verifies its own
GZIP CRC-32 and ISIZE trailer.

The wire proofs preserve the original selected chunk, footer offsets,
frame order and declared slots. The bounded reference decoder retains
the exact nullable mask and accesses the original chunk-local dictionary
in order. Native Arrow V5 readback through EOS preserves the field name,
nullability, tick unit, UTC or local interpretation, and signed counts.
Events retain earlier complete footer groups on failure, and the first
source cause reaches the converter before IPC writer admission. After
successful planning, the first failed data page retains its original
page ordinal and absolute header offset.

## Independent producer and readback

PyArrow 26.0.1 produces nullable UTC nanos with stored CRCs and required
local micros without stored CRCs. Each pinned file contains three
groups, with V2 reference storage flags true, false, and true. Thrift
checks the original codec, annotations and frame extents. zlib checks
the stored CRC, exact member consumption, and the member trailer.
The comparator independently reconstructs the raw masks, exact signed
dictionary words and reference lookups. PyArrow reads the actual
Lean-emitted native IPC through EOS.

Separate mutations damage a raw level byte, damage the GZIP suffix or
dictionary trailer while recomputing the stored CRC, and supply an
invalid dictionary width in a raw suffix. A two-fault control checks
the earlier indexed error. The oracle also verifies that both strict
V1 predecessors keep their refusals and that the V2 entry point
refuses a genuine PLAIN fallback.

[Public theorems](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Dictionary/Gzip/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-gzip-dictionary-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-gzip-dictionary-v2-oracle/fixtures.json) ·
[V1 profile and pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Thms +Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Defs
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-gzip-dictionary-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-gzip-dictionary-v2-oracle/check.py
```
