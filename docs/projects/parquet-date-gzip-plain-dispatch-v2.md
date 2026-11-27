# GZIP DATE V2 dispatch across PLAIN and dictionary groups

`Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain` reads a selected flat INT32
DATE leaf from one checked snapshot. The original row-group and physical
column ordinals determine the dictionary offset used to route that group.
An absent dictionary offset selects the checked PLAIN V2 reader. A present
offset selects the existing V2 dispatcher, which uses the original framed
headers to choose dictionary-only or dictionary-to-PLAIN. The selected
reader validates the column association, span, framing and payload. An
error terminates that route and retains the original typed cause.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/Dispatch/V2/WithPlain/Defs.lean) ·
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/Dispatch/V2/WithPlain/Thms.lean)

The PLAIN and dictionary paths share frame, scalar, row, and stored and
expanded chunk limits. Dictionary and index caps apply to dictionary-backed
groups. Branch agreement covers both exact signed nullable slots and
typed failures under the same snapshot and effective limits. The group
witness retains the original frame chain and page evidence for the chosen
reader, including stored CRC, raw definition levels and the exact
flag-dependent V2 scalar suffix.
[PLAIN V2 reader](parquet-date-gzip-v2.md) ·
[Dictionary-backed V2 dispatcher](parquet-date-gzip-dispatch-v2.md)

Native Date32 readback preserves the descriptor and ordered batches through
EOS. The first indexed source failure retains complete earlier groups and
precedes IPC writer checks.

## Pinned comparison

PyArrow sets dictionary use when it opens a writer. The two mixed files are
explicit test assemblies, each made from a genuine PLAIN-only PyArrow source
and a genuine dictionary-backed source. The comparator checks each parent
independently, copies original chunk bytes verbatim, and rebuilds the
absolute footer offsets. Both nullable CRC-bearing and required CRC-absent
assemblies contain all three profiles. The PLAIN groups exercise raw and
GZIP scalar suffixes. Thrift and zlib verify the frames and payloads, and
PyArrow checks the assembled rows and independently reads Lean-emitted IPC.

Labeled mutations cover CRC failures on all three routes, a wrong PLAIN
compression flag, a PLAIN group falsely claiming a dictionary offset, a
fallback reentry, and damaged groups on two different routes where the
earlier failure wins.
[Comparator](../../scripts/parquet-date-gzip-plain-dispatch-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-gzip-plain-dispatch-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-plain-dispatch-v2/Axioms.lean
python3 -I scripts/parquet-date-gzip-plain-dispatch-v2-oracle/check.py
```
