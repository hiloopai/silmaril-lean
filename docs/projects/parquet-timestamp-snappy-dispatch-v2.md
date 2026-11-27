# Selected Snappy V2 Parquet TIMESTAMP dispatch

`Timestamp.Leaf.Snappy.Dispatch.V2.convert` opts into one checked
modern flat INT64 TIMESTAMP leaf under codec 1. It visits the
selected chunk in footer group order. The original selected column's
dictionary offset chooses the framing path. Without an offset it
uses the strict Snappy PLAIN V2 reader. With an offset it frames
the original bounded chunk once. A PLAIN V2 data header in that
original chain chooses the strict one-way fallback branch. The
other dictionary-backed branch requires RLE_DICTIONARY throughout.
Only the chosen planner and decoder run on the retained frames.

Each branch returns its complete standalone result. Failed footer
lookups and shared dictionary setup errors retain the original
typed cause. Shared setup checks the selected chunk association,
stored chunk cap, complete frame chain, and footer dictionary and
data offsets. Strict admission checks the original V2 headers and
declared group slot totals. Fallback requires a nonempty reference
prefix and a nonempty PLAIN suffix, and rejects reentry.

The resulting wire witnesses retain the original body slices and
any stored CRC, raw definition levels, and the exact literal or
bounded Snappy value suffix selected by the original storage flag.
The dictionary branches use one leading PLAIN dictionary per
chunk. Ordered nullable reference lookups and signed PLAIN words
keep the original ticks. Header and decode stages retain the typed
page coordinates supplied by the chosen reader.

Native Arrow V5 IPC reads through EOS with one batch per original
footer group and the selected field name, nullability, unit,
UTC or local interpretation, and exact signed nullable ticks.
The event trace retains the complete earlier groups before a source
failure, which takes precedence over writer admission.

## Independent evidence

Two genuine PyArrow 26.0.1 files alternate dictionary-only and
one-way fallback groups. Two labeled assemblies interleave unchanged
PLAIN-only chunks from the same producer, updating footer group
positions and counts. Thrift and zlib verify the original headers,
offsets and stored CRCs. PyArrow and an independent hybrid decoder
verify the compressed/literal extents, masks, exact signed values
and group boundaries. Both flags occur for reference and PLAIN data
in each file. PyArrow also reads all four actual Lean-emitted streams
through EOS.

The Lean comparator checks twenty original group decisions, thirteen
typed refusal controls, and ten exact completed prefixes. Separate
mutations check an original data offset, CRCs in each route,
competing failures, and reentry. A labeled V1 assembly exercises the
strict version boundary. Independent source and chunk caps exercise
setup before classification or output.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Snappy/Dispatch/V2/Thms.lean) ·
[Strict dictionary V2](parquet-timestamp-snappy-dictionary-v2.md) ·
[Strict fallback V2](parquet-timestamp-snappy-fallback-v2.md) ·
[Comparator](../../scripts/parquet-timestamp-snappy-dispatch-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-snappy-dispatch-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-dispatch-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-snappy-dispatch-v2-oracle/check.py
```
