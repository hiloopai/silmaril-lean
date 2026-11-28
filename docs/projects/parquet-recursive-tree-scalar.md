# Zero-repetition signed Parquet paths

The [Tree reader](parquet-recursive-tree-rows.md) binds flat signed
INT32 and INT64 fields and signed paths through required or optional
Structs in the same row group as repeated signed siblings. The
physical scanner uses the full original path. A path with zero
repetition has an empty wrapper sequence.

## Original level sections

A V1 level with a maximum of zero consumes zero bytes. The decoder
synthesizes one zero per advertised slot under the existing count
limits, and the next section starts at the same byte. A present
section uses the original four-byte length and exact Hybrid
payload. The V1 section witness describes the consumed bytes for
each of repetition and definition independently, together with
the exact remaining value suffix. It covers original stored
offsets for UNCOMPRESSED data and decoded-body offsets for codecs
with a compressed V1 body.

In V2 an omitted level occupies a zero-length original header
span. The existing level reader checks that length before using
the bounded logical zeros. The row-count check then requires one
row per slot for a zero-repetition path. Definitions still
determine which slots carry signed words. The null-count check
compares that observed absence count with the header. At a zero
definition maximum the original definition length and null count
are both zero. Existing codec, dictionary, checksum, extent and
slot limits apply.

## Rows and projections

The native join matches shared Struct presence from the original
addressed levels. The Struct may be null, present with all children
null, or present with a mixture of scalar and repeated children.
Repeated siblings keep their own cursors, and scalar leaves
contribute one occurrence per row. The existing Tree certificate
recovers every leaf's exact repetition, definition and signed
words. Events and [strict IPC](parquet-recursive-tree-to-ipc.md)
retain original group order, counts and the first typed source
refusal with its selected completed prefix.

## Verification

The pinned PyArrow V1 and V2 files carry required and nullable flat
fields, required and nullable Structs, both signed widths at their
extrema, independently repeated paths, and null versus present
all-null Structs. A labeled reframe combines original V1 and V2
pages within the same group. Independent inputs and emitted IPC
checks verify original frames, exact level spans and signed words,
group counts and strict EOS. Focused format-validation fixtures
check V1 trailing value bytes and V2 omitted-level lengths, row
counts and null counts. A late shared-presence failure keeps both
original leaf addresses. Full, reordered, subset and empty
projections retain the unmodified earlier group, including when
target IPC limits are exhausted.
[Parquet and IPC pins](../../scripts/parquet-recursive-tree-scalar-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-scalar-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-scalar-oracle/check.py
~~~
