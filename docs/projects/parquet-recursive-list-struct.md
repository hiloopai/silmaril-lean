# Shared LIST-of-Struct topology from original Parquet rows

The existing recursive repeated reader admits one canonical LIST whose
element is a Struct of two signed INT32 or INT64 children. The LIST,
Struct and both children have independent required or optional
declarations. Each physical leaf retains its compiled path and original
chunk binding. This slice adds a topology theorem for that shape and
refines error ordering in the existing assembler.
[Recursive schema](parquet-recursive-list-schema.md) · [Repeated row reconstruction](parquet-recursive-repeated-rows.md)

The compiled steps for the LIST and its Struct element form the same
prefix on both physical paths. The shared definition ceiling is one for
the repeated wrapper plus one for each optional common declaration.
An optional child can add one step after this ceiling. On every
successful original row, the two leaf slices have identical ordered
`(repetition, min definition sharedCeiling)` sequences. The minimum
keeps every level below the shared ceiling distinct and identifies
definitions that reach the same present Struct. The exact per-child
projection restores the unclipped levels, classifications and signed
words. The checked group witness retains both physical chunk witnesses,
each original addressed row slice, and the original row count.

The assembler compares live sibling elements in ascending ordinal
order through their common length. It reports an earlier disagreement
in shared presence before any later missing element. At the first
unmatched ordinal, the error identifies the shorter column and the
available counterpart's page, byte and chunk slot. The assembler uses
each column's original partition, so one column can start a new V1
page inside a row independently of the other column.

## Verification

Pinned PyArrow writes unindexed UNCOMPRESSED PLAIN V1 files with both
signed widths and all sixteen nullability combinations. Independent
Compact, CRC, Hybrid and signed-word inspection checks both leaf traces
and original addressed slots across 188 V1 pages from 17 accepted files. The accepted authored reframe places
repetition-one continuations at different slot ordinals in the two
columns. PyArrow and Lean recover the same logical rows in footer order.
The labeled refusals cover null versus empty LIST, null versus present
Struct, unequal length, a case combining earlier presence conflict and
later length mismatch, and swapped physical metadata paths.
[Producer and fixture pins](../../scripts/parquet-recursive-list-struct-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-struct-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-struct-oracle/check.py
~~~
