# Checked native rows for recursive Parquet LIST and Struct trees

`Parquet.RecursiveSchema.Tree.Rows.readGroupChecked` takes a checked
[Tree compiler plan](parquet-recursive-tree-compiler.md) and an original
row-group ordinal. It admits signed paths that have at least one
original LIST wrapper, including paths with a leading Struct.
The adapter retains the original signed INT32 or INT64 column and its
checked V1 or V2 frames. Its existing codec and encoding rules apply to
each physical leaf independently. The result includes the original
footer group, both the declared and decoded slot bounds, the ordered
checked inputs, and the reconstructed logical rows.

## Joining shared occurrences

Each leaf has its own cursor over an array of original slots. Every
slot carries its group, physical column and path, physical frame
ordinal (counting a leading dictionary), absolute header offset, and
cumulative column slot index. A cursor window is a start and stop on
that array. The end of the original chunk also carries its byte offset,
frame count and slot count.

A repetition of zero starts a new row. Within a LIST at repetition
depth `d`, the join takes an element from each descendant leaf up to
the next repetition at most `d`. A higher repetition stays in the
same element and belongs to a descendant LIST. The join walks the
original schema in preorder. For a Struct or LIST it compares each
participating leaf's marker at that declaration, using the shared
definition threshold to distinguish null, empty and present. A
present Struct partitions the windows by its children. An inner
LIST uses only its own descendant windows. Its sibling's element
count and page cuts can differ. Repeated occurrence identities are
the original wrapper ordinals and per-parent element ordinals,
stored innermost first in a refusal address.

The group admission checks its original column count, row count and
total declared slots. It binds every physical leaf in footer order,
then reads each bound leaf in that order. A binding refusal therefore
precedes any payload refusal. After complete column reads, the join
compares rows and visits shared sites in schema and occurrence order.
The first physical column at a site supplies the reference marker or
cursor state, with peers compared in physical order. A shared
cardinality disagreement identifies both the first present occurrence
and the missing side's boundary. If the missing side has reached
the next enclosing occurrence or row, that slot supplies the
boundary. A missing side at the end of its original chunk carries
the chunk-end coordinate. Physical leaf errors pass through with
their typed cause.

## Evidence and bounds

The native reader preflights total declared slots before page reads
and checks the aggregate decoded size before joining. The row count
bounds the row loop, the checked schema depth bounds descent and the
slot budget bounds each LIST iteration. Each cursor scan advances
through disjoint windows at a given repeated depth. The join uses
window offsets over the original arrays. Projection accumulates
per-column slots in reverse and reverses them once. Slot work scales
with the checked slot count times schema depth. Temporary storage
for the addressed inputs, reconstructed rows and projection is
bounded by the admitted slots and schema.

The success certificate independently reprojects the logical rows
through the original schema and compares the full ordered per-leaf
arrays of repetition, definition and exact signed words. It retains
the original ListPath `Wire` and per-page witnesses, and relates each
addressed entry to its original page and local slot. A published
shared topology refusal is the assembler's reached failure after
complete original column reads. Its slot and end coordinates
resolve to those checked original reads.

Zero-repetition paths have a checked compiler plan and a typed
adapter refusal. The [native Arrow Events adapter](parquet-recursive-tree-events.md)
uses the checked group result for its full and projected views.

## Verification

The PyArrow oracle checks a branching LIST of a Struct with
independent signed LIST siblings at unequal repetition depths, and
a second schema with independent top-level LISTs at depths three
and one. It checks multiple groups, required and nullable sites,
null and empty values, and signed extrema. A labeled reframe uses
different V1 continuation cuts and a V2 complete-row range. Each
late topology control keeps all leaf reads valid and checks the
preceding complete group. The controls check original attained
slots and the original chunk end when a shared occurrence is absent.
An independent Compact, Hybrid, CRC and signed-word decode checks
all original frame spans, counters and atoms under test.
[Producer and fixture pins](../../scripts/parquet-recursive-tree-rows-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-rows-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-rows-oracle/check.py
~~~
