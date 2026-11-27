# Bounded compressed Brotli meta-block execution

`Execute.DistanceSwitch.readBlock` accepts a checked compressed meta-block
header and the original cursor at its payload. It executes bounded literal,
insert-and-copy, and distance switching with the existing command executor.
It reuses the MLEN-bounded loop from the literal-switching profile.

Each block initializes its L, I and D runs from the current header. The first
command sees the incoming history and recent-distance ring. Subsequent commands
receive the preceding command's actual state. The block stops exactly at MLEN,
where MLEN measures bytes added by this block. The caller's output cap includes
history, and the bit cap is shared across the entire payload. Commands account
for their output before appending. The first typed command error returns its
original operation offset and zero-based command index.

The API starts after framing and compressed table descriptions. It returns the
original reader at the first untouched payload suffix, including any following
meta-block framing. Static dictionary addresses continue to return a typed
rejection. The earlier command and stream profiles retain their admission gates.
Whole-stream activation needs a proof of failure provenance across the envelope
and is a separate scope.

## Machine-checked contracts

All theorem names below are under
`Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch`.

- `readBlock_sound` gives the ordered command wire decomposition of the exact
  original prefix, untouched suffix and cursor, appended bytes, exact MLEN and
  bit and output limits. Each wire step strictly decreases remaining MLEN,
  even when its command fields consume zero bits.
- `CommandsWire.output` yields exact concatenated output and the bound on
  command count by bytes produced. The chain starts with newly initialized
  runs and threads the complete state across steps.
- `readBlock_error` proves the original bit split for every reported error,
  with earlier successful commands and the first failing stage for an indexed
  command error. It also proves that MLEN fuel cannot mask a command failure.
  `BlockFailure.offset` bounds the command index and preserves the command's
  original operation coordinate.

## Independent replay

The comparator uses pinned libbrotli v1.2.0 at
`028fb5a23661f123017c060daa546b55cf4bde29`. It first replays the independently
assembled command specimen through the public payload reader. A second
assembly reframes that payload into two meta-blocks and starts the second
with an implicit distance-three copy. It checks fresh D runs and inherited
output and recent distances. The two fixtures compare the full output,
block cursor boundaries, distance runs, and final rings.

The test harness uses stream framing to find each payload. A control appends
a trailer byte and verifies the payload reader retains it. Late bit limits,
output limits and truncation pin the original command index and offset. A
separately labeled native-produced dictionary stream pins the typed failure.

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Tests +Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Tests
python3 -B -I -u scripts/brotli-distance-switch-block/check.py
```

The replay accepts `--brotli-source` for an exact checkout of the pinned revision.
[RFC 7932](https://www.rfc-editor.org/rfc/rfc7932)
· [libbrotli pin](https://github.com/google/brotli/tree/028fb5a23661f123017c060daa546b55cf4bde29)
