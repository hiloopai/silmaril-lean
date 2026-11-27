# Brotli compressed command execution

`Brotli.Execute.read` executes one command from a checked compressed
meta-block header with one block type in each category. The caller
provides the standard window field, advertised MLEN, total stream
output at the start of the meta-block, and the cursor at the command
symbol. The state holds the prior stream bytes and the recent-distance
ring. The output cap counts those prior bytes as well as new bytes.
[RFC 7932 §9.3](https://www.rfc-editor.org/rfc/rfc7932#section-9.3)
· [§10](https://www.rfc-editor.org/rfc/rfc7932#section-10)

The executor reads the checked command and literal insertion under
one bit cap, deriving the literal context from the actual output.
If the insertion reaches MLEN, it commits only the literals, carries
the old ring and leaves the rest of the source untouched. Otherwise
it resolves the distance from the post-insertion cursor. An admitted
back reference copies from the prior stream bytes plus the literals.
After each copied byte, the source position is computed from the
now-extended history. A match can overlap itself and can refer across
meta-block boundaries within the available history and window.
[Command](brotli-command.md) · [Literals](brotli-literal.md)
· [Distance](brotli-distance.md)

The executor checks the back-reference output count against MLEN and
the caller cap before appending the byte array or running the copy.
A valid static-dictionary address returns `unsupportedDictionary`
with its distance, word length and word ID. It yields no successor.
The check occurs after distance classification because a dictionary
word's base length can differ from its transformed output length.

`Execute.read_sound` connects the original command, literal and distance
fields to the complete output append and ring transition. It proves
positive output progress, both output bounds, exact bit advance and
the untouched suffix. `Execute.Wire.output_count` gives the exact
appended count. `Execute.copyTail_rejects_overrun` gives the typed
errors before a back-reference append. `HistoryCopy.Wire.byte_at`
identifies each match byte in the prior output plus earlier bytes of
that same copy. The existing Zstandard executor uses the shared
array copy with its existing public match relation and theorem.

The library slice starts after the checked meta-block header and
executes one command. Stream framing, block switching, dictionary
lookup and transformation, and Parquet dispatch are outside it.

## Independent replay

The pinned libbrotli **1.2.0** oracle at
`028fb5a23661f123017c060daa546b55cf4bde29` checks the full output of
four admitted streams from the CLI or streaming encoder. The streams
use distances 1 and 2, a 256-byte literal-only ending, and a flushed
two-meta-block case whose second block starts by copying 768 bytes
at distance 384. The latter starts the copy in the previous block
and continues through overlap. Lean's fixture driver starts from an
empty output and the RFC ring, parses the original framing and headers,
and threads only its own output, counts, ring and cursors. The native
trace is used for comparing bytes, offsets, distances and ring states.
A valid native dictionary stream exercises the typed unsupported
handoff before any output is committed for that command.
[Fixture pins](../../scripts/brotli-execute/fixtures.json)
· [Replay](../../scripts/brotli-execute/check.py)

The fixture driver accepts standard framing for these compressed
streams and empty metadata introduced by the encoder's flush.
The harness imports the existing pinned replay utilities, with
PyArrow **26.0.1** and Thrift **0.25.0** as used by the Brotli lane.

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Execute.Tests +Silmaril.Formats.Compression.Zstd.Sequence.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-execute/check.py
```

Use `--brotli-source /path/to/brotli` to reuse a checkout at the pin.
