# Pageless zero-row groups in recursive signed Parquet

The recursive signed reader admits the exact empty-group convention
observed in PyArrow 26.0.1 files using Data Page V1 or V2. The admitted
schema is still the recursive INT32/INT64, Struct and canonical LIST
profile with at most one repeated ancestor per leaf. Populated chunks
use the existing unindexed UNCOMPRESSED PLAIN readers.

The Parquet IDL defines a chunk's sizes inclusive of page headers,
its first data-page offset, and the deprecated ColumnChunk
`file_offset` (zero when metadata is stored only in the footer).
PyArrow writes a zero `data_page_offset` when there is no page. This
profile interprets zero as a sentinel with no associated byte span.
[Pinned Parquet IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L904-L945)
[ColumnChunk and RowGroup](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1002-L1075)

The version-2 footer has zero rows, both group byte sizes zero, and a
zero group offset for each pageless group. Every leaf keeps its original
physical type and path, has zero slots, both chunk sizes zero, and
zero chunk and page offsets. Its codec is UNCOMPRESSED, its encodings
are `[RLE]`, and its page-encoding stats vector is empty. Raw admission
checks the declared group and chunk fields, including the absence of
external paths, indexes, dictionaries and other auxiliary carriers.
Any declared row-group ordinal must match its footer position. The
positive framed spans tile the original data region in order, from
after the leading magic to the footer. This rejects undeclared bytes
and makes the pageless group leave the current data cursor unchanged.

The default snapshot and positive interval check continue to require
framed chunks. Recursive open checks that policy first, then checks
the pageless convention on the original footer when a strict interval
check fails and there is an exact typed empty-group candidate.
`Snapshot.checkRecursive_exact` preserves the original metadata and
every group ordinal. `groupStop_empty` certifies the original ordered
column declarations and raw group check. `Chunk.Wire.noSpan` proves
the admitted empty chunk has no pages and no interval under the
standard span check. The existing GroupWire, Events and IPC readback
laws apply to the empty group as well as the surrounding groups.
The writer continues to emit framed V1 empty pages.

## Fixtures and regressions

Four genuine pinned PyArrow files exercise page versions V1 and V2
with statistics enabled and disabled. Each has an explicit middle
group with zero rows between groups of three and two rows. The
surrounding chunks use checksums. Independent Compact Thrift inspection
checks each physical path and the exact empty metadata and body
coverage. Lean reads those bytes with zero page, slot, row and chunk
budgets for each pageless column. Native rows, direct Events, empty
projection and complete Lean-emitted Arrow IPC retain `[3, 0, 2]`.
PyArrow reads each emitted IPC stream and independent framing checks
its batch counts and exact EOS. Labeled edits cover count, size,
placeholder, dictionary, index, external path, positional declaration
and undeclared-byte refusals. The V2 predecessor fixture still tests
the strict snapshot refusal and its labeled framed-zero admission.

```sh
lake build --wfail +Silmaril.Formats.Parquet.Footer.PageLessRecursive.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-pageless-oracle/Axioms.lean
python3 scripts/parquet-recursive-pageless-oracle/check.py
```
