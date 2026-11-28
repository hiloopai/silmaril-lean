# Native Parquet V1 for a canonical signed LIST path

`ListPath.openFile` compiles the original footer. Given that source,
`ListPath.Reader.readAll` reads one signed INT32 or INT64 leaf in a
positive-depth canonical LIST path. Each LIST and the leaf retain their
original names and independent REQUIRED or OPTIONAL markers. The
reader returns one logical Arrow observation per original row group,
in footer order.
[Schema and logical trace core](parquet-recursive-list-path.md) · [Arrow Events](parquet-recursive-list-path-events.md)

The V1 route reads local, unindexed UNCOMPRESSED PLAIN Data Page V1
with Hybrid repetition and definition levels. The reader checks the
original column path, physical type, codec, encodings, data offset and
positive chunk span. The bounded page scanner parses the original
headers and consumes exactly that span. Each page verifies its optional
CRC on the original stored body. The level decoders use the compiled
path's repetition and definition maxima. The signed PLAIN decoder
consumes the entire value suffix and assigns one word per terminal
definition in original slot order.

The page witness binds the absolute repetition and definition spans
including their four-byte prefixes, the independent Hybrid witnesses,
and the exact signed suffix to the original file. The chunk witness
retains the contiguous page chain, both column footer sizes including
headers, and exact row and slot counts. Limits cover header, page,
section, body, chunk, row and slot budgets.

## Row boundaries

Repetition zero starts a row. A positive repetition continues only a
wrapper reached by both the prior slot and the current definition.
The cursor carries this ancestry across original V1 pages. A physical
zero-slot page has no effect on the cursor. Reconstruction takes the
trace of the complete group, so a legal page split preserves the rows
when the plan and trace agree.

Schema-only files have no chunks to read. This geometry requires an
original positive-sized in-file chunk for every group. Pageless groups,
external chunks, dictionaries, indexes and other value encodings are
outside the native profile. The same reader also supports complete-row
V2 pages and the bounded codec profiles. [Native V2 reader](parquet-recursive-list-path-v2.md) · [Codec profiles](parquet-recursive-list-path-codecs.md)

## Verification

Lean directly reads 46 genuine PyArrow files and a labeled V1 reframe.
Independent Compact, Hybrid, CRC and signed-word inspection checks
255 original pages at depths 1, 2, 3, 4, 6, 15 and 16. All sixteen
nullability choices at depth three pass at both widths. Depth one
and two agree with the existing native observations. The reframe
crosses page starts at repetitions one, two and three inside a row,
adds a trailing physical zero-slot page, and reads back in PyArrow.
Genuine schema-only and CRC-absent files also pass.

Twenty-five typed controls cover original page addresses, missing ancestry, wire extents, CRC, counts, offset and footer
sizes, and admission limits. Genuine files exercise the refusals for
indexes, Brotli and dictionary encoding. The late word and CRC edits
leave the earlier group readable and make the ordered file read return
the original page error.
[Producer and fixture pins](../../scripts/parquet-recursive-list-path-v1-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-v1-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-v1-oracle/check.py
~~~
