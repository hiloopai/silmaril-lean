# Strict Arrow V5 IPC to canonical signed LIST-path Parquet

`ListPath.Writer.FromIpc.convert` accepts a strict binary recursive Arrow V5
IPC stream for one named canonical LIST chain over signed INT32 or INT64.
The original schema and every complete ordered record batch pass to the
checked ListPath writer after the source has reached an exact modern
eight-byte EOS. A schema-only stream produces zero groups. A zero-row
record batch produces one physical zero-slot page at its original group
position. [Recursive IPC reader](arrow-recursive-stream.md) · [ListPath writer](parquet-recursive-list-path-writer.md)

Each result group is one unindexed UNCOMPRESSED PLAIN V1 page of complete
rows with optional stored-body CRC. The original names, signed widths
and per-node nullability survive native readback. Null and empty lists
remain distinct at each depth. The IPC reader and Parquet writer use
their independent depth, work and size budgets. The writer profile
continues to exclude other root shapes, multiple leaves, additional
encodings and codecs, and indexed or pageless groups.

## Original carrier and readback guarantees

The open error carries the original IPC schema cause. A terminal
failure carries the original trace, with the complete prefix and the
first failing record ordinal, byte offset and typed cause.
`convert_terminal_wire` binds those fields to the original carrier.
`convert_writer_wire` establishes exact source EOS and the original
writer result when the writer refuses the conversion.

`convert_readback` binds the actual IPC schema, consecutive records
and exact terminal offset to the constructed Parquet bytes and their
checked native readback. Direct IPC and Parquet Events agree on the
declaration, ordered batches and EOS. When the full-field forward
bridge succeeds, it returns the same observations through its own
strict EOS. [Forward bridge](parquet-recursive-list-path-to-ipc.md)

## Verification

Pinned PyArrow and independent FlatBuffer inspection verify 20 original
V5 streams at depths 1, 2, 3, 4, 6 and 16, with both signed widths.
PyArrow and independent Compact, Hybrid, CRC and signed-word checks verify
39 native Parquet pages, including a physical empty group between
populated ones. The 20 Lean-emitted return streams are inspected through
exact EOS, including their original-equivalent values and canonical
validity, LIST offsets and signed-word buffers. Twenty typed controls
exercise malformed opening and later records, EOS truncation and
trailing bytes, source limits, wrong target shapes and writer budgets.
Later source failures are checked with both ordinary and exhausted target
budgets. [Producer and original and emitted byte pins](../../scripts/parquet-recursive-list-path-from-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.FromIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-from-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-from-ipc-oracle/check.py
~~~
