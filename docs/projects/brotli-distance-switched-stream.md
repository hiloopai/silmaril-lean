# Exact Brotli streams with all block-switch categories

`Stream.DistanceSwitch.decode` is an opt-in decoder for one exact RFC 7932
standard-window stream. It uses the existing stream envelope and the checked
distance-switching meta-block executor. Compressed blocks admit literal,
insert-and-copy, and distance switching. Static dictionary addresses return
a typed failure. The earlier stream entry points keep their admission guards.

Each compressed meta-block initializes its category runs from its header.
It receives the actual output history and recent-distance ring from the
preceding meta-block. A raw block appends its bytes and preserves the ring.
A metadata block consumes its aligned body and preserves both. The first
last flag ends the stream after exact zero fill through the byte boundary.
The decoder rejects any trailing input.

Input bytes, window size, absolute bit position, cumulative output and total
meta-block count are caller-bounded. The envelope checks raw and compressed
declared output extents against the remaining capacity. Each compressed
header has its own context-entry and tree caps. Command execution receives
the remaining payload bit cap. Errors return the first typed operation and
its absolute bit coordinate. A failed command includes zero-based block
and command indices.

## Machine-checked contracts

The theorem names below are in
`Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch`.

- `Payload.output` gives exact appended bytes and declared MLEN.
- `decode_sound` witnesses the original window and meta-block bits, exact
  terminal padding, ordered concatenated output, inherited history and ring,
  fresh category state and cumulative caps.
- `decode_error` witnesses the first failed operation. The success prefix
  records earlier checks and complete earlier blocks. A compressed command
  failure retains the checked tables, earlier successful commands, and
  original typed failure. `FailureWire.offset` splits the original bits at
  the reported position for envelope and command failures.

## Independent replay

The reference is libbrotli v1.2.0 at
`028fb5a23661f123017c060daa546b55cf4bde29`. The native-produced specimens
exercise distance switching alone and all three categories. The oracle
traces confirm that both are dictionary-free. The separately labeled
assembled fixtures exercise an implicit copy across compressed meta-blocks
and the raw and metadata paths. The Lean comparison calls the whole-stream
entry point with the original bytes and caps and compares complete output and
the final recent-distance ring.

The controls cover late distance switch failures, truncated input, raw and
terminal padding, trailing input and cumulative cap boundaries. A separate
native-produced stream exercises typed static dictionary rejection. The
pinned fixtures also check the earlier stream entry points' refusal of
distance-switching inputs. Parquet activation is outside this profile.

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Tests
python3 -B -I -u scripts/brotli-distance-switched-stream/check.py
```

The replay accepts `--brotli-source` for an exact checkout of the pinned revision.
[RFC 7932](https://www.rfc-editor.org/rfc/rfc7932)
· [libbrotli pin](https://github.com/google/brotli/tree/028fb5a23661f123017c060daa546b55cf4bde29)
