# Canonical signed Parquet LIST paths

`Parquet.RecursiveSchema.ListPath.openFile` compiles the original Compact
footer of a single signed INT32 or INT64 leaf under a positive number of
canonical LIST ancestors. Every LIST and the leaf independently admit
REQUIRED or OPTIONAL. The compiler shares the checked LIST annotation,
wrapper and signed-leaf rules with TwoList. It consumes the original
entries in preorder and retains their names, nullability, ordinals and
paths. The physical schema-depth budget includes the root, two entries
for each LIST, and the leaf. The default budget of 32 admits 15 LIST
ancestors. A larger configured budget supports longer canonical paths.
[One-LIST compiler](parquet-recursive-list-schema.md) · [TwoList reader](parquet-recursive-two-list.md)

## Logical trace

`ListPath.Rows.project` emits the canonical ordered repetition and
definition levels with an aligned optional signed word at each slot.
The first child inherits the enclosing repetition. Each later child
uses the depth of its own repeated wrapper. At every LIST, a nullable
node can stop at its optional step, an empty list stops at the wrapper,
and a nonempty list reaches the child. The signed leaf uses its own
optional step or the terminal definition. The threshold proofs bind
these steps to the same Dremel context used by the existing compiler.

`ListPath.Rows.reconstruct` partitions the complete trace at row and
child starts. It checks the claimed row count and verifies that the
result projects back to every original level and aligned word. The
two inverse laws recover the original rows or trace under the row and
slot budgets. The proof also establishes Arrow typing, signed-word
order and exact projected slot demand before trace allocation.

The footer and logical trace core also serves the bounded native
unindexed PLAIN V1/V2 reader with UNCOMPRESSED and Snappy columns.
[Native V1 reader](parquet-recursive-list-path-v1.md) · [Native V2 reader](parquet-recursive-list-path-v2.md) · [Snappy](parquet-recursive-list-path-snappy.md)

## Verification

Pinned PyArrow produced 44 genuine positive files at depths 1, 2, 3, 4,
6, 15 and 16. The depth-three inputs cover all sixteen nullability
choices at both widths. Independent Compact, Hybrid, CRC and signed-word
inspection checked 243 original V1 pages. The oracle passes the
extracted traces to Lean for 88 logical round trips and compares the
depth-one and depth-two observations with the established native
readers. The depth-two comparison also checks each original slot.

Eighteen typed controls cover genuine out-of-profile schemas and depth
limits, plus authored logical traces with illegal continuation, wrong
width, missing words, bad counts and budget failures.
[Producer and fixture pins](../../scripts/parquet-recursive-list-path-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-oracle/check.py
~~~
