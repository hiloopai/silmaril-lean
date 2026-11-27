# Checked recursive Parquet LIST schema

`Parquet.RecursiveSchema.Repeated.openFile` binds the original footer
of a checked immutable snapshot to a recursive Arrow declaration and
ordered physical leaf plans. The staged profile adds canonical
three-level LIST to the existing signed INT32/INT64 and required or
optional unannotated Struct grammar. The standalone LIST check
recognizes a modern LIST annotation with an absent or matching
legacy converted code. The list group has one child, an unannotated
REPEATED group named `list`, which itself has one element. The
element is required or optional and can be an integer or a Struct.
Different paths may contain separate Lists. Each physical leaf path
admits at most one repeated wrapper.
[Parquet LIST encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#lists)

The ordered Arrow tree retains the exact names and separate
nullabilities of the outer List and its element. Its sole child is
the element declaration. The physical leaf path retains every
original component, including the wrapper and element, and excludes
the root. Positional leaf order is physical preorder. Raw REPEATED,
nested LIST ancestry, unsupported annotations, noncanonical wrapper
shapes, and unsupported physical types return typed errors. Footer
validation still checks original chunk paths, ordering and schema
depth. Depth counts the physical wrapper.

An optional declaration contributes one definition step. An
unreached optional site identifies an absent node, null List, null
element, or absent descendant inside a present element. An
unreached repeated wrapper distinguishes an empty List. The maximum
definition level is the number of steps and identifies a present
signed word. The maximum repetition level is one on a List path and
zero elsewhere. Repetition zero marks a row start. Repetition one
marks a continuation and must reach past the empty-list level, even
if the element itself is null. The classifier works on individual
level pairs. Page decoding and checking that a continuation has an
open predecessor remain separate.

The grammar consumes the original typed and raw schema items in
order. The step laws refer to the original item ordinals, paths and
annotation, including the original repeated wrapper and the exact
empty-list index. The overlap laws relate nonrepeated classification
and the standalone nullable INT32 LIST level pairs to their staged
counterparts. The existing nonrepeated compiler and standalone
reader remain independent.

## Reproduce

```sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-schema-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-schema-oracle/check.py
```

Pinned PyArrow produces the original nested Parquet files. The
comparator checks actual footer bytes independently through
PyArrow and Thrift, including ordered paths and maximum definitions
and repetitions. The Lean runtime checks all four combinations of
List and element nullability, a Unicode element name, Structs in
and around LIST, and local level-pair classifications. It also
compares the same original nonrepeated and standalone LIST files
through their existing entry points. Labeled edits isolate raw
repetition, bad outer and wrapper shapes, and a conflicting
ConvertedType. Genuine files cover unsupported annotation and
nested repeated ancestry.
[Fixture pins](../../scripts/parquet-recursive-list-schema-oracle/fixtures.json)
