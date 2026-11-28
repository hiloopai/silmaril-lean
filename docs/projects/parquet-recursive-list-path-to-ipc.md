# Native signed LIST-path Parquet to strict Arrow V5 IPC

`ListPath.Reader.ToIpc.convert` runs the existing native signed
LIST-path Events reader and passes its selected trace to the shared
recursive Events-to-IPC adapter. The source profile is unindexed
UNCOMPRESSED PLAIN V1/V2 with one signed leaf. Full-field selection
retains the nested LIST declaration and logical values. Empty selection
emits a zero-width schema and one explicit record count per original
row group, including a zero-row batch for a physical empty group.
[Native V1 reader](parquet-recursive-list-path-v1.md) · [Native V2 reader](parquet-recursive-list-path-v2.md) · [Source Events](parquet-recursive-list-path-events.md)

The adapter reaches the source terminal before admitting the target.
An open refusal carries its original cause. A native read failure
retains its typed error and every complete selected batch before it.
The error result contains no IPC carrier. On source EOS, the existing
recursive writer admits the selected schema and ordered batches under
the independent IPC limits. Writer refusals retain their typed cause
and any original batch ordinal.
[Recursive stream writer](arrow-recursive-stream-writer.md)

## Readback

The conversion proof binds the actual source footer and native group
witnesses to one ordered IPC observation per original group. The
strict writer readback certifies the selected declaration, exact
logical batches and counts, and one eight-byte modern EOS at the end
of the emitted carrier. Direct projected Events and IPC Events agree
on the positional field names and declarations, full batch
observations and EOS. The shared selection laws identify the exact
empty rows at width zero.

## Verification

Nine pinned native Parquet sources at depths three, four, six and
sixteen cover both signed widths, nested nulls and empties, schema-only
input, an explicit physical empty group, and a labeled legal V1
reframe. PyArrow and independent FlatBuffer and buffer inspection
check 18 Lean-emitted streams, including original record counts,
signed words, LIST offsets, validity, zero padding and exact EOS.
The original and reframed sources produce equal bytes under both
selections. Appended and truncated EOS controls preserve the failure
offset from strict readback.

Labeled later-page word and CRC refusals preserve the original native
coordinates and complete earlier group under both projections and
exhausted IPC limits. The empty carrier preserves its open refusal.
Eight typed writer controls cover batch count, first and later record
row limits, declaration depth and physical slot budget.
[Producer, original Parquet and IPC pins](../../scripts/parquet-recursive-list-path-to-ipc-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-to-ipc-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-to-ipc-oracle/check.py
~~~
