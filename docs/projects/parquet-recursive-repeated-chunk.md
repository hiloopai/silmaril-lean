# Checked repeated signed Parquet V1 chunks

`Parquet.RecursiveSchema.Repeated.Chunk.bindChunk` binds a selected
physical leaf and row group from the recursive LIST schema compiler to
the original column chunk. The binding retains the original column
ordinal, path, signed INT32 or INT64 type, counts and byte span. The
chunk must have codec UNCOMPRESSED, advertise PLAIN with only PLAIN
and RLE entries, and have no dictionary or legacy index page offsets.
Both ordinary and repeated leaves in the compiled schema are admitted.
[Recursive LIST compiler](parquet-recursive-list-schema.md)

The shared chunk walk also admits the checked V2 profile.
[Recursive V2 reader](parquet-recursive-v2.md)

The reader refuses an advertised
OffsetIndex or ColumnIndex at binding. V1 pages may begin within a
row when there is no OffsetIndex. The indexed rule requires a row
boundary. The reader retains a live element-bearing List state across
each admitted boundary, including an empty page. A null element
occupies a slot and can be followed by a continuation. A null or empty
List and an absent ancestor leave no live List. Each chunk starts with
the state closed.
[Pinned V1 and V2 page rules](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L697-L762)

Each original V1 page must use PLAIN values with RLE level headers
and equal compressed and uncompressed sizes. The reader checks the
stored CRC when present. Each nonzero level maximum requires its own
four-byte length and bounded hybrid section, repetition first and
definition second. Zero maxima omit the corresponding section.
The exact signed PLAIN suffix fills only the slots classified as
values. The returned optional word list aligns with the ordered
repetition, definition and classification records.

`ColumnMetaData.num_values` counts all level entries. The reader
charges each page against the remaining entries before decoding it.
`RowGroup.num_rows` counts repetition-zero starts. The reader checks
the independent row ceiling during classification and requires both
totals at the original end of the chunk. Separate chunk byte, page,
level, slot and row bounds apply. A page failure retains the original
group, column, path, page ordinal, header byte offset and page-start
slot. Local classification failures and row overruns also identify
the failing global slot.

The wire laws bind the consecutive original pages, length words and
hybrid sections, exact value suffix, original slot order and live
transition at each pair. Successful traversal attains both footer
counts within the page budget. The scope ends at one selected column
chunk.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-repeated-chunk-oracle/Axioms.lean
python3 scripts/parquet-recursive-repeated-chunk-oracle/check.py
```

Pinned PyArrow and independent Thrift, hybrid and signed-word
inspection compare each original page with events derived from
PyArrow's nested rows. Genuine checksummed sibling chunks cut pages
at different rows. The spec-authored unindexed continuation preserves
six level entries and describes three rows across four pages. PyArrow
agrees with that layout. The labeled controls check invalid first
continuation, continuation after an empty List, mismatched slot and
row counts, extent and word errors, CRC corruption and independent
limits. A genuine indexed file checks the index refusal.
[Fixture pins](../../scripts/parquet-recursive-repeated-chunk-oracle/fixtures.json) ·
[Authored continuation and native variants](parquet-list-continuation.md#native-and-authored-fixtures)
