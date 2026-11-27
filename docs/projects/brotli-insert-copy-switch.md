# Checked Brotli block-type selection and insert-and-copy switching

`BlockTypes.Switch.select` handles the three RFC 7932 block categories.
Each category has its own current type, previous type and remaining run
length. A checked multi-type control starts with current type 0,
previous type 1 and the header's initial count. The fixed single-type
path starts with the RFC maximum MLEN as its quota. Each call reserves
one coded symbol. A positive remaining count consumes no switch bits.
At zero, a multi-type run reads a type symbol, the count symbol and
its extra bits under the caller's residual bit budget. The type symbol
selects the previous type, the incremented type with wraparound, or an
explicit ordinal. The new run stores the old current type as its
previous type and debits the symbol from the new count.
[RFC 7932 §6](https://www.rfc-editor.org/rfc/rfc7932#section-6)
· [§9.3](https://www.rfc-editor.org/rfc/rfc7932#section-9.3)

`Switch.select_sound` preserves both other category states and
accounts for the exact original switch prefix and untouched suffix.
`Switch.read_error` and `Switch.select_error` retain the category,
cause and absolute operation start. A count error points to the
cursor after the validated type code. `BlockTypes.readLength`
reuses the header's count reader, including the wire bound of
1–16,793,840 symbols per run.

## Insert-and-copy command execution

`Execute.InsertCopy.read` admits switching in the insert-and-copy
category with single literal and distance block types. It selects
from the original command group and presents that single tree to the
existing command executor. The literal and distance paths retain the
original context maps, parameters and trees. The adapter debits
switch bits before command execution and returns the switched state
only after command, literal, distance and copy processing succeed.
The execution state carries the stream output and recent-distance
ring. The caller supplies the meta-block extent and cumulative
output cap. Initialize the category state from the checked header at
each meta-block boundary.

`selected_tree_exists` derives an in-range 704-symbol table from
the existing checked header contract. `Execute.InsertCopy.read_sound`
joins the switch witness and selected tree to the existing byte-output
law, exact cursor and cumulative bounds. `Execute.InsertCopy.read_error`
witnesses lower errors at the original cursor. A command failure points
to the start of the command after the switch. The one-command API
takes an original bit cursor. The caller owns block and command indices.

Literal and distance switching in execution return distinct errors.
The shared primitive already maintains all three histories. Whole-stream
dispatch, meta-block-wide validation of the declared type set, static
dictionary materialization, and Parquet activation are separate.
[Existing stream profile](brotli-stream.md)

## Independent replay

Two independently assembled RFC 7932 streams are pinned with libbrotli
**1.2.0**, commit `028fb5a23661f123017c060daa546b55cf4bde29`. The
first exercises increment, previous-type reuse, an explicit ordinal
and increment wraparound across executed commands. The second uses a
zero-bit type code and a two-command switched run, exercising the
header seed for previous type. The native decoder supplies output,
type histories, remaining lengths and cursor positions. The Lean
driver derives its header, state, commands, output and cursors from
the input bytes. Controls cut the type code, exhaust the bit cap in
the type and count stages, and exhaust the output cap after a
successful switch prefix. Lean guards also cover a truncated count,
invalid ordinal, invalid state, and category isolation.
[Fixture pins](../../scripts/brotli-insert-copy-switch/fixtures.json)
· [Replay](../../scripts/brotli-insert-copy-switch/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Tests +Silmaril.Formats.Compression.Brotli.Execute.InsertCopy.Thms +Silmaril.Formats.Compression.Brotli.Stream.Defs
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-insert-copy-switch/check.py
```

Use `--brotli-source /path/to/brotli` to reuse the pinned checkout.
