# Exact Brotli streams with insert-and-copy switching

`Brotli.Stream.InsertCopy.decode` is the opt-in standard-window decoder
for compressed meta-blocks with multiple insert-and-copy types and
one literal and one distance type. It uses the same window, raw data,
metadata, compressed table header and final padding checks as
`Brotli.Stream.decode`. The first last flag ends the stream and
the final zero fill consumes the rest of the input. The original
single-type decoder keeps its public result, wire and error types.
[RFC 7932 §§9.1–9.3](https://www.rfc-editor.org/rfc/rfc7932#section-9)
· [Single-type stream profile](brotli-stream.md)

Each checked compressed header initializes its own command category
state and initial run count. The checked executor reads the switch
when the count reaches zero, selects the original command tree, and
debits the switch bits from the remaining command budget. Stream
bytes and the four recent distances carry across meta-blocks. Raw
data enters the byte history and metadata leaves the execution state
intact. The stream applies cumulative input, output, committed-bit
and meta-block caps. The compressed table limits apply per meta-block.
Each successful command emits bytes, so the declared MLEN bounds
command fuel even with singleton codes.
[Insert-and-copy executor](brotli-insert-copy-switch.md)

`Stream.InsertCopy.decode_sound` accounts for the original input
through the final zero fill, the ordered byte chunks, and cumulative
bounds. `CommandsWire.output` bounds command count by emitted bytes,
and `Payload.output` gives the exact declared meta-block size.
The wire relation starts every compressed payload from its own
checked header and the inherited execution state.

`Error.envelope` carries the ordinary framing or header error.
`Error.command` carries the zero-based meta-block and command
indices and the original typed lower error. A switch count error
reports the absolute start of the count, and a command error after
a switch reports the absolute start of the command. The theorem
`decode_command_error` witnesses every successful preceding block
and command and the first failed operation. `decode_command_offset`
ties the reported bit to the original input prefix.

This slice leaves literal and distance switching, static dictionary
materialization, and Parquet activation for later. The admitted
profile uses the checked type ordinal range and leaves validation
that every declared type appeared to a separate end-of-meta-block
check.

## Independent replay

The switched fixture is independently assembled from RFC fields
and differentially decoded by libbrotli 1.2.0 at
`028fb5a23661f123017c060daa546b55cf4bde29`. It contains two
compressed meta-blocks separated by nonempty metadata. The second
has a different initial count, type code and command tree order.
Its first implicit-distance command copies four bytes from the
previous meta-block. The Lean driver passes the complete source
bytes directly to the public decoder. Native traces locate six
switches and pin typed failures at the original offsets, including
a truncated count in the second block and a capped command after
a complete switch. The replay compares both public decoders on
six no-switch predecessor streams and checks the existing dictionary
control and native literal/distance switching rejections.
[Fixture pins](../../scripts/brotli-switched-stream/fixtures.json)
· [Replay](../../scripts/brotli-switched-stream/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Tests +Silmaril.Formats.Compression.Brotli.Stream.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-switched-stream/check.py
```

Use `--brotli-source /path/to/brotli` to reuse the pinned checkout.
