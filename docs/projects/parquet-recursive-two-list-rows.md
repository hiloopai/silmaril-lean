# Logical Arrow batches from checked two-LIST Parquet chunks

The two-LIST reader can reconstruct one logical Arrow batch per original
row group. The output uses the existing recursive Arrow cells and batch
observation type. The Arrow schema retains the outer field, inner element
and signed leaf names and nullability from the checked Parquet plan.
Present scalar cells retain their original INT32 or INT64 width.
[Two-LIST chunk profile](parquet-recursive-two-list.md)

Reconstruction flattens the checked pages into one ordered trace of
repetition, definition and optional signed words. It starts a row at
repetition zero and a new inner element at repetitions zero and one
within the row. Repetition two extends the current inner list. Null and
empty lists become distinct Arrow cells at both levels, and a null leaf
becomes a null scalar cell.

An independent projection walks the completed Arrow rows using only their
declaration and nested logical cells. Each row projects one initial
repetition zero. Later inner elements start at one, and later leaves in
that inner list use two. The projection uses the original definition
thresholds for null and empty sites and copies present signed words in
order. Before returning a batch the reader checks that this projection
reproduces the entire original atom trace and that the row count matches
the original footer.

The proofs bind each atom to both original level streams and its aligned
word, establish that successful rows fit the declared Arrow schema and
preserve the ordered signed words, and tie each batch to its original
position and row count. For any two accepted page splits of the same
ordered trace, both checked row counts are the number of repetition-zero
atoms and the reconstruction results agree. The existing Events and IPC
routes retain their current scope. This slice uses the existing
unindexed PLAIN geometry and writer policy.
[Original V1/V2 page checks](parquet-recursive-two-list-v2.md)

## Fixtures and regressions

Pinned PyArrow supplies all eight nullability combinations at each signed
width. Independent Compact, Hybrid and signed-word inspection checks the
original fields and slot traces. Lean's logical batches match PyArrow's
nested rows and per-group counts. Two labeled reframings preserve the
original rows while starting pages at repetitions one and two, including
after a null leaf. A stale inner continuation retains its original typed
chunk error. Other controls check the inherited slot cap and the semantic
checks for missing words, signed width, counts and malformed traces.
[Producer and fixture pins](../../scripts/parquet-recursive-two-list-rows-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-two-list-rows-oracle/Axioms.lean
python3 scripts/parquet-recursive-two-list-rows-oracle/check.py
~~~
