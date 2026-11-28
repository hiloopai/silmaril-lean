# Checked Parquet LIST and Struct tree compiler

`Parquet.RecursiveSchema.Tree` uses the original checked footer
traversal in `Repeated` for canonical three-level LIST declarations,
unannotated Structs, and signed INT32 and INT64 leaves. Leaf repetition
depths can differ in the same schema. The compiler consumes the exact
physical preorder, including LIST wrappers. The existing
`Repeated.compile` entry point selects its single-wrapper admission
and keeps its `nestedRepeated` refusal before examining the second
wrapper. Unsupported annotations, types, schema extents and depth
violations retain their original typed errors.

Each leaf plan has its positional column index, physical SchemaElement
ordinal and path, signed kind, and ordered Struct and LIST ancestry.
Original ordinals identify declarations, so different sibling sites
keep different identities even if their display names coincide.
Nullable sites carry their definition stop. Each LIST carries its
empty definition stop and uses its one-based position in the repeated
ancestry as its repetition level. The maximum definition reaches the
signed value. The maximum repetition is the number of repeated
ancestors. The proofs cover exact preorder, complete signed-leaf
coverage and order, original typed and raw footer items, unique
ordinal identity, and identical ancestry and level-step prefixes
through a shared original ancestor.

## Executable leaf adapter

`Tree.bindLeaf` binds a selected physical column by its original
row group and index, then checks the original path, kind, codec,
encoding and bounded carrier span. `Tree.readLeaf` uses the existing
checked ListPath page reader and retains its original frames, cursors,
levels and signed words. The projection proof preserves the exact
step list, definition and repetition maxima and wrapper thresholds.

ListPath's carrier requires a leading LIST. A path beginning with a
Struct or a signed leaf still has a complete checked compiler plan
and returns a typed representation refusal from the leaf adapter.
The compiler module depends on the footer traversal. The adapter
imports the ListPath decoder separately.

## Shared-occurrence join

The [native row-group join](parquet-recursive-tree-rows.md) uses these
plans and independent leaf observations. It joins shared original
sites by row and occurrence, retains independent descendant cursors,
and checks exact projection back to the signed physical slots.

## Verification

The pinned PyArrow fixture uses
`LIST<STRUCT<a: INT32, b: LIST<INT64>, c: LIST<INT32>>>`. The
three leaves have repetition depths 1, 2 and 2, and the sibling
lists have unequal and independent lengths. Independent Compact,
Hybrid, CRC and signed-word inspection checks the original V1 and
V2 pages through the leaf adapter. Other genuine fixtures check a
leading Struct and a typed DOUBLE refusal. The branching fixture
checks the depth limit and the legacy nested-LIST refusal.
[Producer and fixture pins](../../scripts/parquet-recursive-tree-compiler-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Thms +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-compiler-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-compiler-oracle/check.py
~~~
