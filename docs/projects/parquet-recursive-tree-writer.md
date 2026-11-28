# Checked native Parquet writer for signed Trees

`Parquet.RecursiveSchema.Tree.Writer.emit` accepts a named Arrow
declaration of signed INT32 and INT64 fields, Structs and canonical
LISTs, together with an ordered list of explicit row-group
observations. It emits an unindexed UNCOMPRESSED PLAIN V1 Parquet
file. Each supplied group contributes one physical group, with one
complete page per signed leaf. A physical zero-row group has one
zero-slot page per leaf. An empty list of groups produces a
schema-only file.

## Construction

The writer uses the existing Compact schema planner and footer
assembler. It opens a schema-only carrier through the checked Tree
compiler. That opening supplies the original leaf order, physical
paths, widths and level thresholds. The exact recursive declaration
must equal the caller's input before row groups are built.

The shared `Tree.Rows.Projection` traversal first counts the physical
slots required per column and then retains the exact signed traces.
The preflight checks row counts and per-column, group and cumulative
slot limits before storing the trace. Both modes walk the same
schema and cells. Independent sibling LISTs therefore contribute
their own lengths and each nullable ancestor contributes the
original definition transition. The group certificate records the
checked count and trace.

The shared V1 page writer checks level and payload sizes before
allocating bytes. A level section at width zero occupies zero
bytes. Present sections use the usual length-prefixed Hybrid runs.
The page writer checks the Compact header and the total frame extent
before adding it to the file. The footer records the actual
header-inclusive extent as both stored and raw size, with the
original data-page offset. The Compact footer and PAR1 envelope are
assembled within the remaining file budget.

## Readback

The public emitter reopens the actual output with the original
Tree reader. It checks the immutable bytes, compiled declaration,
footer, and explicit original group count. Each group is fully
decoded in footer order. Its observation must equal the caller's
input, and its checked original signed atoms must equal the
construction's full ordered repetition, definition and word
traces. The readback proof retains those exact group results
and their original physical column witnesses.

## Verification

The pinned oracle checks actual Lean-emitted PAR1 files with
PyArrow and independent wire parsing. The cases include both
signed widths and extrema, scalar and repeated siblings, nullable
Structs beside present all-null Structs, independent LIST lengths,
nested LISTs, a physical zero-row group and schema-only output.
The independent inspection checks original page frames, CRC,
level spans, exact words, per-column anchors and sizes, and the
contiguous payload and footer boundary. Typed controls exercise
malformed declarations and rows and group, column, row, slot
and byte limits.
[Producer and output pins](../../scripts/parquet-recursive-tree-writer-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-writer-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-writer-oracle/check.py
~~~
