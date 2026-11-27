# Selected uncompressed Parquet TIMESTAMP V2 dispatch

`Timestamp.Leaf.Uncompressed.Dispatch.V2.convert` opts into per-row-group
dispatch for one modern, flat INT64 TIMESTAMP leaf with codec 0. The
original selected footer column's dictionary offset selects the framing
path. A chunk with no dictionary offset uses the strict PLAIN V2 reader.

A dictionary-backed chunk frames its original bounded bytes once. One
traversal of the original data headers records whether a PLAIN V2 header
occurs and produces either the ordered header plan or its first indexed
error. Classification can therefore use a later PLAIN V2 tag even when
an earlier header failed planning. Without a PLAIN V2 tag, the header
plan agrees with strict dictionary-only planning. With that tag, the
existing fallback phase check requires a nonempty dictionary-reference
prefix followed by a nonempty PLAIN suffix. The phase and row-count
checks use the retained plan. The chosen body reader neither reframes
the chunk nor retries another decoder.

The dispatcher is equal to the selected standalone reader on success and
failure. Successful groups retain the original contiguous frames, offsets,
CRC-covered stored slices, exact V2 raw definitions and literal value
extents. Footer and framing failures, planner errors, and later checksum
or decode failures keep their original typed causes. The first failed
group gives an Events trace with all preceding complete batches and
takes precedence over sink admission. Native IPC readback keeps the
selected UTC or local descriptor, signed nullable ticks and one ordered
batch per original footer group through EOS.

## Independent evidence

Six genuine PyArrow 26.0.1 files cover PLAIN-only, dictionary-only and
one-way fallback for nullable UTC nanoseconds and required local
microseconds. Thrift, zlib and independent Hybrid decoding check the
original frames. Two labeled mixed-profile files copy the original
selected chunks byte for byte and rewrite their footer offsets. PyArrow
independently reads both assemblies and all eight Lean-emitted streams.
The six homogeneous streams are also compared byte for byte against
the applicable standalone writer output.

The controls cover original CRC faults in all three profiles, competing
late faults, reentry, an earlier malformed header before a later PLAIN
tag, a labeled V1 assembly, codec refusal, and original setup errors.
The comparator checks thirty group decisions, fifteen typed refusal
controls and thirteen complete prefixes.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Uncompressed/Dispatch/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-uncompressed-dispatch-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-uncompressed-dispatch-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-uncompressed-dispatch-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-uncompressed-dispatch-v2-oracle/check.py
```
