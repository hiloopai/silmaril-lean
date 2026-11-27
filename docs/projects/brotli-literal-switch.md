# Checked Brotli literal and insert-and-copy switching

`Execute.LiteralSwitch.read` executes a compressed command with
independent literal and insert-and-copy runs. It reads the I switch
and command first, then checks the full insertion's output debit.
Before each literal it selects and debits the L run through
`BlockTypes.Switch`. The selected type identifies the mode and
the row of the original context map. The last two output bytes
give the context within that row. The resulting original tree
supplies the Huffman code and the next byte. The executor reuses the
existing distance and overlap-copy tail on the original header.
[RFC 7932 §6](https://www.rfc-editor.org/rfc/rfc7932#section-6)
· [§7.1](https://www.rfc-editor.org/rfc/rfc7932#section-7.1)
· [§9.3](https://www.rfc-editor.org/rfc/rfc7932#section-9.3)

`Literal.Switch.readOne_sound` puts the exact switch bits before the
context-selected byte code. `Literal.Switch.Wire.carry` keeps the I
and D histories while updating byte history after each literal.
`Execute.LiteralSwitch.read_sound` composes the I switch, command,
L selections and optional distance/copy tail under the bit and output
caps. Reaching MLEN through literal insertion ends the command before distance lookup.

`readBlock` is the bounded compressed-payload entry point. It receives
the checked compressed header, stream execution history, and declared
meta-block length. It initializes fresh L/I/D runs, preserves the
existing stream bytes and recent distances, and threads each accepted
command's actual successor into the next. `readBlock_sound` proves
the declared extent, ordered output, exact bit suffix and command
fuel bound. The length comes from the checked outer framing.

`read_error` witnesses the first failing stage within a command. A
literal failure follows only successful earlier literal reads and
precedes any distance/copy operation. `readBlock_command_error` does
the same for the first failing command. `Failure.offset` and
`BlockFailure.offset` identify the original bit with the matching
input prefix. The reported bit is the start of the failing operation.
A switch count failure points just after its type code. A literal
code failure points just after the switch.

The executor admits one distance type. Distance switching and static
dictionary references produce typed errors. The public stream
dispatchers and the default Parquet codec retain their previous
profiles. Validation that every declared type appeared is outside
this payload executor.
[Prior stream profile](brotli-switched-stream.md)

## Independent replay

The specimen is independently assembled from RFC fields. Libbrotli
1.2.0 at `028fb5a23661f123017c060daa546b55cf4bde29` supplies the
independent output and bit trace. Both compressed meta-blocks have
multiple L and I types. A literal switch occurs inside an insertion,
another run continues into the next command, and both runs reset
at the second meta-block. A copy changes the next literal's context
within the same L type and causes a different tree selection.
The trace compares bytes, mode, context, tree, current/previous
type, remaining count, and bit positions. Separate controls cover
I and L count caps, a cap after a successful L switch, an output
guard that takes precedence over a literal cap, late truncation,
native D switching, and a native static dictionary reference.
[Fixture pins](../../scripts/brotli-literal-switch/fixtures.json)
· [Replay](../../scripts/brotli-literal-switch/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-literal-switch/check.py
```

Use `--brotli-source /path/to/brotli` to reuse the pinned checkout.
