# Exact Brotli streams with literal and command switching

`Stream.LiteralSwitch.decode` is an opt-in bounded decoder for a single
standard-window Brotli stream. It uses the RFC 7932 §§9.1–9.3 envelope shared
with `Stream.InsertCopy` and the checked `Execute.LiteralSwitch.readBlock`
payload executor. The compressed profile admits literal and insert-and-copy
block-type switching with one distance type. Distance switching and static
dictionary references retain distinct typed errors. The earlier stream
decoders and Parquet codec profiles retain their original entry points.

Each compressed meta-block starts its own category runs from its checked
header. It inherits both the accumulated output bytes and the recent-distance
ring. A raw block appends its bytes and preserves the ring. A metadata block
accounts for its aligned bytes and preserves the entire execution state.
The first last flag requires zero fill to the byte boundary and exhausts the
supplied input. Errors carry no partial output.

## Bounds and checked laws

The envelope checks input bytes, window size, absolute input bits, accumulated
output, and total meta-blocks. Raw and compressed blocks check their declared
output extent against the remaining capacity before decoding their bodies.
Each compressed header has per-block context-entry and Huffman-tree caps.
The payload executor receives the residual bit cap and uses the declared
output extent as command fuel, including singleton codes with zero input bits.

The theorem names below are in `Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch`.

- `Payload.output` ties the fresh-run payload witness to exactly the appended
  bytes and the meta-block's declared length.
- `decode_sound` witnesses the original window and block bits, exact final
  padding, ordered concatenation, and input, output, window, and block caps.
  Each block receives the previous block's actual output and recent-distance
  ring. Each block header consumes bits, bounding block count by input length.
- `decode_error` proves that the reported absolute offset splits the original
  source. For a command error it also witnesses all earlier successful
  meta-blocks and commands up to the first lower failure, including the
  original cursor and typed literal, switch, or copy error.

## Independent replay

The comparator pins libbrotli v1.2.0 at
`028fb5a23661f123017c060daa546b55cf4bde29`. Unmodified libbrotli checks the
full decoded bytes. The existing pinned trace instrumentation records the
block extents, command and switch positions, and recent-distance ring.
The Lean comparator invokes the public whole-stream decoder with only
the original bytes and caps.

The streams are assembled from RFC fields independently of the Lean decoder.
The two-block literal and insert-and-copy specimen comes from the checked
block profile. A second assembly adds raw and metadata blocks, reframes the
same two switched payloads and ends with a zero-bit command that reads the
previous block's most recent distance. It overlaps at distance one and
produces different bytes than a copy at the default initial distance of four.
The insert-and-copy-only predecessor is also replayed through both decoders.

The failure controls cover late literal and command switch caps, late
truncation, invalid final fill, trailing input, cumulative output/bit/block
caps, input cap, and pinned native-produced distance-switching and dictionary
streams. The manifest records the original byte pins and reported positions.

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Tests
python3 -B -I -u scripts/brotli-literal-switched-stream/check.py
```

The comparator accepts `--brotli-source` for an existing exact checkout of the
pinned revision. [RFC 7932](https://www.rfc-editor.org/rfc/rfc7932)
· [libbrotli pin](https://github.com/google/brotli/tree/028fb5a23661f123017c060daa546b55cf4bde29)
