# Bao combined whole-object completeness

`Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Thms` extends the
[range fact API](bao-range-facts.md) for the official unkeyed Bao combined
layout. The encoder uses `Bao.encode .combined` with a reference callback
that reads bytes by slot and recomputes each requested child CV. It is not a
streaming encoder or a performance implementation.

`Combined.complete` applies to every payload actually named by the concrete
BLAKE3 digest when its byte length is less than `2^64` (part of `Named`) and
at most the verifier cap. There is no restriction to powers of two, full-sized
final chunks, or positive lengths. The geometry is `geometry 0 size`, with an
empty leaf for size zero and one data field per original 1024-byte chunk.

The proof identifies the official full plan with the canonical chunk tree,
serializes each parent as its two non-root CVs using absolute chunk counters,
and discharges the strict parser's header, body-length and slot checks. It
then replays those same fields in verifier order, applying ROOT only at the
top and obtaining checked EOF by reaching the rightmost leaf. Projecting
the resulting contiguous data for `Request.toEnd 0` returns exactly the named
payload, plus its authenticated extent.

This is an encoder-to-wire-to-range API theorem for **whole-object combined
responses**, not a general multi-chunk theorem for all windows or encodings.
To extend it to other combined requests, the remaining adapter is a projection
theorem for a contiguous tape and an arbitrary in-bounds request: after each
prefix, the cursor is the consumed byte position clamped to the requested
window, and the coverage is that prefix's intersection with the window. Bao
slice and outboard additionally need their own scheduling/serialization
bridges; raw Iroh retains the typed grouped theorem and its existing tests.

```sh
lake build --wfail +Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Thms +Silmaril.Formats.Iroh.Vectors
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/BaoCombinedCompleteness.lean
```
