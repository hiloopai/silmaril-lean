# Bounded Brotli stream decoding

`Brotli.Stream.decode` checks one complete RFC 7932 stream. It accepts
standard window headers (10 through 24 bits), uncompressed data blocks,
metadata blocks, and compressed blocks with one block type in each
category and backward references. It begins with the RFC distance
ring and an empty output. It passes the actual source cursor, output
and ring between blocks. Raw bytes enter history without modifying
the distance ring. Metadata contributes neither history nor output
and preserves the ring. The last flag triggers final zero-fill and
whole-input checks. This includes last compressed or metadata blocks
and an empty last block.
[RFC 7932 §§9.1–9.3](https://www.rfc-editor.org/rfc/rfc7932#section-9)
· [§10](https://www.rfc-editor.org/rfc/rfc7932#section-10)

The limits cover input bytes, the standard window in bytes, complete
output, committed source bits and total meta-blocks, including
metadata and an empty last block. The decoder debits a data block's
declared size before executing or copying its body. Byte extents are
checked against the residual bit budget before slicing. The fixed
framing fields can inspect up to 31 bits before their cursor commit.
The existing compressed header and command readers receive only the
remaining bit budget. Compressed header map-entry and tree limits
apply per meta-block. Command fuel starts at MLEN because every
accepted command appends at least one byte even if it consumes zero
bits. The API retains the full prior output within the caller's
output limit. These limits describe logical decoder extents.

`Stream.decode_sound` links the original bits, the ordered output
chunks and ring transitions, and the checked caps. `BodyWire.output`
gives each block's exact regenerated extent. `CommandsWire.output`
and `BlocksWire.progress` bound command count by emitted bytes and
meta-block count by consumed bits. `Stream.decode_error` witnesses the
reported absolute bit as a cursor into the original input and
identifies the guarded operation or lower decoder error. The completed
block and command paths count the zero-based indices. Coordinates
mark the start of the failing operation, including the start of the
final fill for a trailing-input error. The decoder returns a state
only on complete success.

Static dictionary addresses and block switching have distinct typed
errors. Large-window extensions and concatenated streams are outside
the profile. The raw-only decoder and the individual command decoder
remain independently callable. This profile has no Parquet dispatch.
[Command profile](brotli-execute.md)

## Independent replay

The replay builds libbrotli 1.2.0 at
`028fb5a23661f123017c060daa546b55cf4bde29`. It compares decoded bytes
and the final distance ring on six admitted streams. Two producer
streams contain both raw and compressed blocks, separated by metadata
emitted through the public encoder API. The earlier two-compressed-block
fixture and the raw-to-compressed stream both copy 768 bytes at distance
384 after the first block emits 512 bytes. Native traces establish block
types, byte counts, boundaries and failure coordinates. The Lean entry
point receives the original stream bytes and caller caps. It derives
history and the output independently. The replay checks late truncation,
a wrong MLEN, final fill and trailing input, all three cumulative caps,
and native switching and dictionary controls. The Lean guards also
check authored metadata, standard-window and alignment edge cases.
[Fixture pins](../../scripts/brotli-stream/fixtures.json)
· [Replay](../../scripts/brotli-stream/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Stream.Tests +Silmaril.Formats.Compression.Brotli.Tests +Silmaril.Formats.Compression.Brotli.Execute.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-stream/check.py
```

Use `--brotli-source /path/to/brotli` to reuse the pinned checkout.
