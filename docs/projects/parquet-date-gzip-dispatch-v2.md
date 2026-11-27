# Per-group GZIP DATE dispatch with V2 data pages

`Parquet.Date.Leaf.Gzip.Dispatch.V2` reads a checked selected flat INT32
DATE leaf through an explicit opt-in entry point. Each row group comes
from the same checked snapshot and original selected chunk with its
leading GZIP PLAIN dictionary. The presence of a PLAIN V2 data header in
the original frame list selects the existing dictionary-to-PLAIN planner.
Otherwise the existing dictionary-only V2 planner applies. The chosen
planner validates the frame versions and encoding sequence before any
body is decoded. A failure returns the original error from that route.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/Dispatch/V2/Defs.lean) ·
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/Dispatch/V2/Thms.lean)

For a selected and framed group, the dispatcher agrees with the chosen
dedicated reader on checked plans, decoded slots, and typed failures.
The same agreement proofs serve the V1 and V2 dispatchers. Group witnesses
retain the original chunk, frame chain, offsets and caps. The selected V2
page witnesses retain the original stored CRC, raw definition levels and
exact scalar suffix. A true compression flag requires one bounded GZIP
member for the suffix. A false flag uses the original suffix bytes. The
required or nullable mask and dictionary indices or PLAIN values account
for every signed optional day.
[Dictionary-only V2](parquet-date-gzip-dictionary-v2.md) ·
[Dictionary fallback V2](parquet-date-gzip-fallback-v2.md) ·
[Per-group V1 dispatch](parquet-date-gzip-dispatch-v1.md)

Native Date32 readback preserves the field descriptor and exact
footer-order groups through EOS. The first indexed source failure retains
complete earlier groups and precedes IPC writer checks. Failures after
framing retain their original page ordinal and header offset. A framing
failure carries its original group index and typed cause.

## Pinned comparison

Two genuine PyArrow files have dictionary-only, fallback and dictionary-only
groups. The dictionary-only reference suffixes are raw. The fallback group
has compressed references and both raw and compressed PLAIN suffixes. The
nullable CRC-bearing and required CRC-absent cases both preserve signed
endpoints. Thrift and zlib independently check the original frame and
payload transitions, and PyArrow reads back native Lean IPC.

Labeled mutations cover raw level CRC failures, inner trailers with valid
outer CRC, flag and level-extent errors, reentry, and two corrupt groups
where the earlier failure wins. Genuine V1 and PLAIN-only files exercise the
admission boundary.
[Comparator](../../scripts/parquet-date-gzip-dispatch-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-gzip-dispatch-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-dispatch-v2/Axioms.lean
python3 -I scripts/parquet-date-gzip-dispatch-v2-oracle/check.py
```
