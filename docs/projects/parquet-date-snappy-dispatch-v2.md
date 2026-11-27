# Selected Snappy Parquet DATE V2 profile dispatch

`Parquet.Date.Leaf.Snappy.Dispatch.V2` binds one flat INT32 DATE leaf by
physical ordinal in one checked snapshot. A selected footer column
without a dictionary offset uses the strict PLAIN reader. For a
dictionary-backed column, the shared checker frames the original chunk
once. A PLAIN V2 data header selects the strict one-way fallback plan.
Otherwise the checker uses the dictionary-only plan. The chosen reader
consumes the retained frames and returns its result directly.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Snappy/Dispatch/V2/Defs.lean) ·
[Strict PLAIN V2](parquet-date-snappy-plain-v2.md) ·
[Strict dictionary-backed V2](parquet-date-snappy-dictionary-v2.md)

The agreement laws identify the complete result of the strict branch,
including typed setup, header and body errors. If framing fails before
header selection, either dictionary-backed profile returns the same
setup error. Success is equivalent to success in one of the three strict
readers and retains that reader's original frames, CRCs, raw levels and
flag-selected Snappy or literal suffixes. The first indexed source
failure retains all earlier complete event groups and precedes writer
limits. Date32 IPC preserves the original descriptor and each ordered
batch of signed nullable slots through EOS.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Snappy/Dispatch/V2/Thms.lean)

## Pinned comparison

The mixed-profile file is a labeled assembly from four genuine PyArrow
26.0.1 parents. The comparator independently verifies each parent and
copies the selected original row-group chunks byte for byte, relocating
the footer offsets. Six groups cover all three strict profiles, with
both storage flags in each fallback phase. Thrift, zlib, PyArrow and the
independent Hybrid comparator check the original data. PyArrow reads the
assembly and the Lean-emitted IPC.

Twelve controls compare exact strict results, original failure
coordinates and completed prefixes. They include CRC and reference
mutations, a forged dictionary offset, reentry ahead of a later invalid
header and a bad dictionary CRC, a framing cap before profile selection,
and genuine V1 and GZIP refusals.
[Comparator](../../scripts/parquet-date-snappy-dispatch-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-snappy-dispatch-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true \
  tests/formats/parquet-date-snappy-dispatch-v2/Axioms.lean
python3 -I scripts/parquet-date-snappy-dispatch-v2-oracle/check.py
```
