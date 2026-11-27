# Opt-in per-group Snappy V2 dispatch for Parquet LIST

`ListFile.Multi.Snappy.DispatchV2.convert` reads the canonical nullable
LIST of nullable signed INT32 and emits one native V5 Arrow LIST batch per
row group. It frames the original local chunk once against the immutable
checked Snapshot. The first original frame selects the dictionary arm
if it is a dictionary page. Within that arm, a later PLAIN Data Page V2
header selects the one-way dictionary-to-PLAIN reader. The PLAIN arm
requires the dictionary offset to be absent. The dictionary arms verify
both advertised offsets before reading the dictionary. The footer's
encoding summary plays no part in selection.
[PLAIN V2](parquet-list-snappy-v2.md) · [Dictionary V2](parquet-list-snappy-dictionary-v2.md) · [V2 fallback](parquet-list-snappy-dictionary-fallback-v2.md)

The chosen reader checks its own V2 tags, original CRC if present, raw level
spans, suffix compression flag, slot and row totals, and expanded size.
A later header can select the fallback arm, but the arm still validates
bodies in original frame order and rejects dictionary reentry. The same
remaining expansion budget crosses each profile transition and the
dictionary body counts toward that budget.

## Proof and error order

The checked group proof ties header classification to the selected original
frame list and carries the existing profile's exact nested row and budget
witnesses. The read-result equations propagate the chosen reader's exact
error with its profile tag and original coordinates. The dispatcher invokes
one reader per group. Full-chunk framing precedes routing. After routing,
an earlier invalid body in that group retains precedence over later page
errors. A late group error retains the completed batches in the source
trace and precedes native writer admission. Successful output preserves
the field descriptor, group order, nullable list and child slots, and exact
native EOS.

The dispatcher is a separate entry point. Its scope is local Snappy chunks,
the canonical LIST schema and Data Page V2. The individual profile APIs
retain their admission conditions.

## Pinned producer and assembled control

PyArrow 26.0.1 produced a native file with dictionary-only and fallback
groups, and a separate native PLAIN-only file. Its dictionary setting
applies to the column for that writer. The labeled all-profile control
copies the native chunk bytes unchanged, changes their absolute offsets
in a rebuilt footer, and keeps every original page header and stored CRC.
Thrift independently checks the original page order, exact extents and
counts in all three files. PyArrow reads the inputs and Lean's V5 IPC
output, including null lists, empty lists, null children and signed INT32
endpoints.

The negative controls mutate stored bytes in each arm and retag the last
fallback page to test reentry. A combined mutation confirms that an earlier
indexed CRC failure takes precedence over late reentry. The Lean guards
cover the cumulative cap across all three profiles, writer refusal,
V1 refusal and the existing profile selectors.
[Dependency pins](parquet-flat-page.md#independent-page-fixtures) · [Fixture hashes and observations](../../scripts/parquet-list-snappy-v2-dispatch/observations.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Examples
replay=$(mktemp -d)
python3 scripts/parquet-list-snappy-v2-dispatch/Oracle.py "$replay" |
  diff -u scripts/parquet-list-snappy-v2-dispatch/observations.txt -
```
