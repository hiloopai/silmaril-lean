# Selected mixed GZIP and Zstandard V2 Parquet TIMESTAMP

`Timestamp.Leaf.MixedCodec.V2.convert` opens a checked modern flat INT64
TIMESTAMP leaf by serialized schema ordinal. For each footer row group,
it reads the original codec of that group's selected column. Codec 2
uses the strict GZIP V2 dispatcher. Codec 6 uses the strict Zstandard
V2 dispatcher. Other codec IDs produce a typed error carrying the
original number. Each group runs one decoder. The selected dispatcher
admits PLAIN, RLE_DICTIONARY with one leading PLAIN dictionary, or
one-way dictionary-to-PLAIN fallback according to its existing rules.

The two codec limits are independent. The relevant strict dispatcher
checks the original chunk association and frame intervals, verifies a
present stored-body Parquet CRC, and applies its raw-level, literal or
compressed suffix, size, row, and codec integrity checks. The mixed
reader retains the codec's complete typed cause and adds the original
footer group index. Individual page causes retain the coordinates
reported by that strict reader. `trace` includes exactly the complete
batches preceding the first source error, and `convert` checks the
source through EOS before admitting the writer.

Native Arrow V5 IPC preserves one batch per original group, the
selected field name and nullability, the exact unit and UTC or local
interpretation, and the ordered signed nullable ticks. It reads back
through native EOS. The existing single-codec entry points and the
default reader retain their strict admission.

## Independent evidence

The comparator uses eight pinned PyArrow 26.0.1 producers from the
two strict dispatchers. Two labeled mixed-codec assemblies copy
unchanged genuine column chunks, updating footer group positions and
counts. Each assembly alternates codecs and exercises all six
codec/profile combinations, with nullable UTC nanoseconds in one and
required local microseconds in the other. The producer comparators
check the stored extents, CRCs, raw masks and flag-selected payloads
using Thrift, zlib and libzstd. Thrift independently checks the
assembled selected codecs and frame identities. PyArrow reads the
assembled Parquet groups and the actual Lean IPC output, including
signed INT64 endpoints and original batch cuts.

Separate controls check late original CRC failures in each codec,
competing cross-codec failures, damaged unselected data, a genuine
Snappy chunk, genuine V1 chunks from both codecs, and independently
tight codec budgets. The Lean driver checks 18 selected group reads,
11 typed refusals and eight exact completed prefixes. PyArrow reads
three emitted streams, including the unselected-damage control.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/MixedCodec/V2/Thms.lean) ·
[GZIP dispatcher](parquet-timestamp-gzip-dispatch-v2.md) ·
[Zstandard dispatcher](parquet-timestamp-zstd-dispatch-v2.md) ·
[Comparator](../../scripts/parquet-timestamp-mixed-codec-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-mixed-codec-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-mixed-codec-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-mixed-codec-v2-oracle/check.py
```
