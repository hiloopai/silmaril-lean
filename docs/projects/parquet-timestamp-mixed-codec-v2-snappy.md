# Selected Snappy, GZIP and Zstandard V2 Parquet TIMESTAMP

`Timestamp.Leaf.MixedCodec.V2.WithSnappy.convert` opts into Snappy
(footer codec 1), GZIP (2), and Zstandard (6) for a single selected
modern flat INT64 TIMESTAMP leaf. Each row group reads the original
selected column's codec ID once. Only that codec's strict V2
dispatcher runs on the same bound leaf. Its existing PLAIN,
dictionary-only, and one-way fallback rules govern admission.

The group result retains the chosen dispatcher's complete typed
cause, including original frame ordinals, absolute offsets, and
CRC failures where the codec reports them. Unsupported codec IDs
retain their original number. A successful group retains the
same-snapshot frame, bound, stored CRC and nullable slot witnesses
from the strict dispatcher. The dictionaries, definition masks
and flag-selected suffixes remain tied to the original bytes.

The prior two-codec entry point uses the same footer lookup, GZIP
and Zstandard routing, and output policies. The compatibility laws
cover a group whenever the selected lookup does not return codec 1,
including failed lookups and unsupported codec IDs. For a file
whose selected groups all meet that condition, the trace preserves
the prior batch list and termination under the explicit error
embedding. The new converter preserves the complete two-codec
result under that embedding, including identical successful IPC
bytes, source open errors, and writer refusals.

The source trace retains exactly the earlier complete footer groups
before the first indexed source failure. That failure precedes
writer admission. Successful native Arrow V5 IPC reads through
EOS with the selected field name, nullability, time unit, UTC or
local interpretation, and exact signed nullable ticks in footer
batch order.

## Independent evidence

Two labeled three-codec assemblies cover all nine codec/profile
combinations in different footer orders. Each selected chunk comes
from a pinned genuine PyArrow 26.0.1 producer, through the
unchanged-chunk fixtures used by the strict dispatchers. Thrift and
zlib confirm the original codec IDs, frame identities and stored
CRCs in the assemblies. PyArrow independently reads every selected
Parquet group and all six Lean-emitted streams through EOS,
including two native Snappy inputs and two prior two-codec
assemblies. The prior assemblies also produce byte-identical IPC
through the two public converters.

The comparator checks 38 selected groups, twelve typed refusal
controls and nine complete prefixes. Separately labeled mutations
exercise late and competing CRC failures across codecs. Labeled
assemblies exercise a late Snappy V1 chunk and an unsupported codec
in the two-codec domain. The earlier converter's source-open,
writer, GZIP and Zstandard failures compare exactly after lifting
their typed errors.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/MixedCodec/V2/WithSnappy/Thms.lean) ·
[Two-codec profile](parquet-timestamp-mixed-codec-v2.md) ·
[Snappy V2 dispatch](parquet-timestamp-snappy-dispatch-v2.md) ·
[Comparator](../../scripts/parquet-timestamp-mixed-codec-v2-snappy-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-mixed-codec-v2-snappy-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-mixed-codec-v2-snappy-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-mixed-codec-v2-snappy-oracle/check.py
```
