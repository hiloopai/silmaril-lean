# Brotli distance resolution

`Brotli.Distance.read` resolves one pending copy under the RFC 7932
standard-window profile with one distance block type. It takes the
checked compressed header and command, the window field and total
stream output through the command's literals, the recent-distance ring,
and the source cursor. A literal insertion that reaches MLEN has no
pending copy. [Literal insertion](brotli-literal.md)

For an explicit distance, the copy length selects a context
`min (CLEN - 2) 3`. The original distance map selects the checked
Huffman tree. The symbol is followed by zero extra bits for short or
direct codes, and by the RFC §4 little-endian field for a regular code.
The reader uses one cap for the code and its extras. A regular field
uses at most 24 bits, and the complete explicit read uses at most 39.
An implicit distance uses symbol zero and the latest distance without
advancing the cursor. A nonpositive short-code result is rejected.
[RFC 7932 §4](https://www.rfc-editor.org/rfc/rfc7932#section-4)
· [§7.2](https://www.rfc-editor.org/rfc/rfc7932#section-7.2)

The ring begins with `[4, 11, 15, 16]` in most-recent-first order at
stream start. The caller carries it across meta-blocks. A nonzero
distance symbol pushes the resolved distance only for a back reference.
Explicit and implicit symbol zero and all dictionary addresses leave
the ring unchanged.

Distances from 1 through `min (2^WBITS - 16) produced` yield a
`backReference`. Greater distances yield a separate `staticDictionary`
address when the copy length is 4–24 and the RFC word ID fits the
Appendix A word count and 121 transforms. The address contains the
original distance, word length and word ID. Dictionary data lookup
and transformation, history-byte copying, block switching, and
Parquet dispatch are outside this profile.
[RFC 7932 §8](https://www.rfc-editor.org/rfc/rfc7932#section-8)
· [Appendix A](https://www.rfc-editor.org/rfc/rfc7932#appendix-A)

`Distance.read_sound` witnesses the actual selected tree, original
code and extra bits, exact advance, and untouched suffix. It also
proves that an implicit distance preserves the complete cursor.
`Wire.resolved`, `Resolved.valid` and `Resolved.back_bounds` establish
the classification, address, history bounds and ring update.
`Ring.start_positive` and `Resolved.ring_positive` prove positivity
of the initial and successor rings.

## Independent replay

The pinned comparison observes distance symbols, extra bits, context
and tree selection, exact offsets, output history extent, classification,
word IDs, and the recent-distance ring before and after the native read.
Lean starts with the RFC ring and threads its own successor. It re-reads
the checked header and each original command tree. The native trace
supplies command and post-literal cursor positions and produced counts
because this slice omits producing the intervening bytes. Positive-width
distance reads also get a one-bit-short cap check.

Seven producer streams exercise implicit distance, explicit symbol
zero, short and direct codes, all four regular postfix widths,
multiple trees within one distance block type, and static-dictionary
addresses. The inputs include two real PyArrow payloads, one ordinary
CLI stream, and four streams from the pinned libbrotli encoder API.
The replay pins libbrotli **1.2.0** at
`028fb5a23661f123017c060daa546b55cf4bde29`, PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`.
[Fixtures](../../scripts/brotli-distance/fixtures.json)
· [Replay](../../scripts/brotli-distance/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Distance.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-distance/check.py
```

Use `--brotli-source /path/to/brotli` to reuse a checkout at the pin.
