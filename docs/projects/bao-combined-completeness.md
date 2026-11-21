# Bao combined range completeness

`Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Thms` extends the
[range fact API](bao-range-facts.md) for the official unkeyed Bao combined
layout. The encoder uses `Bao.encode .combined` with a reference callback
that reads bytes by slot and recomputes each requested child CV. It is not a
streaming encoder or a performance implementation.

`Combined.completeWindow` applies to every payload actually named by the concrete
BLAKE3 digest when its byte length is less than `2^64` (part of `Named`) and
at most the verifier cap. There is no restriction to powers of two, full-sized
final chunks, or positive lengths. The geometry is `geometry 0 size`, with an
empty leaf for size zero and one data field per original 1024-byte chunk.
Every in-bounds request is covered: exact bounded requests, including proper
interior and zero-count windows, and `toEnd` requests starting at or before EOF.
`Combined.complete` is the `toEnd 0` specialization.

The proof identifies the official full plan with the canonical chunk tree,
serializes each parent as its two non-root CVs using absolute chunk counters,
and discharges the strict parser's header, body-length and slot checks. It
then replays those same fields in verifier order, applying ROOT only at the
top and obtaining checked EOF by reaching the rightmost leaf. EOF is available
even for interior requests because the **combined frame** reveals the right
edge, not because the requested response finished. The resulting `Done` remains
geometry-indexed and `Done.seal` requires matching checked extent.

`Projection.project` is reusable for any contiguous segment of a checked tape,
including nonzero bases: after each prefix the cursor is the consumed absolute
position clamped to the requested window, and the bytes are the intersection
with that window. `Projection.range` turns a completed tape whose contiguous
span covers the request into a staged exact range, without any EOF premise or
conclusion.

This is a combined-wire theorem, not a general multi-chunk slice or outboard
theorem. The remaining slice bridge must replay the encoder's pruned preorder
through the real verifier, with `Contiguous` for the selected chunks and EOF
only when the rightmost data leaf is revealed. It must also establish the
slice-specific framing guard on the serialized fields. The executable
regression encodes and decodes a proper multi-chunk interior slice without
EOF; that is a test, not a general slice proof. Raw Iroh retains the typed
grouped theorem and its existing tests.

```sh
lake build --wfail +Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Thms +Silmaril.Formats.Iroh.Vectors
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/BaoCombinedCompleteness.lean
```
