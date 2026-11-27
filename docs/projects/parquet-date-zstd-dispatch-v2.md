# Selected V2 Parquet DATE Zstandard profile dispatch

`Parquet.Date.Leaf.Zstd.Dispatch.V2` uses one checked snapshot and
one selected flat INT32 DATE ordinal. The original footer column's
dictionary offset chooses the PLAIN or dictionary-backed reader.
The PLAIN route uses the existing strict V2 reader. The dictionary
route frames the original selected chunk once and chooses the
strict dictionary-only or fallback plan from those parsed headers.
A PLAIN V2 header selects fallback, whose plan checks the required
reference prefix and PLAIN suffix. The selected plan and decoder
return any failure directly.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Zstd/Dispatch/V2/Defs.lean)

The strict admitted profiles agree with the dispatcher on the exact
ordered signed nullable slots. The branch laws also preserve the
typed setup, header and decode errors on the original frames.
The original frame chain carries the selected reader's physical
witnesses for stored CRC, raw definition levels and the exact
flag-selected suffix. The leading dictionary witness uses the
same checked snapshot. Native Date32 IPC preserves the original
descriptor and each footer-order group through EOS. The first
indexed source error retains its complete earlier event prefix and
precedes writer limits.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Zstd/Dispatch/V2/Thms.lean) ·
[PLAIN V2](parquet-date-zstd-v2.md) ·
[Dictionary-only V2](parquet-date-zstd-dictionary-v2.md) ·
[Fallback V2](parquet-date-zstd-fallback-v2.md)

## Pinned comparison

PyArrow selects dictionary use when it opens a writer. The mixed
file is a fixture assembly built from three genuine PyArrow 26.0.1
parents. Each parent is checked independently. The assembly copies
original chunk bytes verbatim and adjusts the footer's absolute
offsets. Six groups cover all three routes, including both V2 flags
in the PLAIN parent and in both phases of the fallback parent.
Thrift, libzstd, zlib and the independent Hybrid reader check the
original parents. PyArrow checks the assembled file and independently
reads the Lean-emitted Date32 IPC.

Ten labeled mutations cover stored CRCs on all routes, false
dictionary routing metadata, a wrong compression flag and reentry
before a damaged dictionary. A two-route corruption checks footer
error precedence. Each control compares the strict route's result
and exact completed group prefix.
[Comparator](../../scripts/parquet-date-zstd-dispatch-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-zstd-dispatch-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-zstd-dispatch-v2/Axioms.lean
python3 -I scripts/parquet-date-zstd-dispatch-v2-oracle/check.py
```
