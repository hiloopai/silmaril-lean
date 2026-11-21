# Bao range facts: integration experiment

This is a follow-up to [the wire/CAS integration](blake3-wire-cas.md), originally
at `fad3de0054acc7f55aab0aaa8eece5d684d0db17` ([#1600](https://github.com/hiloopai/silmaril-lean/pull/1600)).
Review only the new `Blake3Cas.RangeFacts` modules, proofs and regression. The underlying
BLAKE3 range kernel ([#1583](https://github.com/hiloopai/silmaril-lean/pull/1583)),
EOF judgment ([#1586](https://github.com/hiloopai/silmaril-lean/pull/1586)), and
Bao/Iroh format model ([#1587](https://github.com/hiloopai/silmaril-lean/pull/1587)) are prerequisites,
not changes here. This experiment does not change naming semantics or join two kernel openings.

## API and meaning

Use `Silmaril.Formats.Blake3Cas.RangeFacts.Thms`. A `Request.bounded start count` asks for
exactly `[start, start + count)`; `Request.toEnd start` asks for the suffix. Resolving a
request into a window using a header is scheduling, not verification of that header.

| Result | Meaning |
| --- | --- |
| `Done claim digest request` | The frame and requested projection are complete at the claimed geometry. `done.bytes` is still staged. `finishPrefix?` checks the actual read prefix, cursor, pending slots, remaining bytes and caller-supplied frame boundary. |
| `Extent digest size` | The existing checked right-edge proof. It can be obtained from a cell before frame completion, or independently from another frame with the same digest and extent. |
| `Bounded digest start stop` | Exact bytes at an absolute half-open interval, with no extent in the result. `Done.seal` and `sealSpan` use matching extent evidence. `slice?` bounds-checks a subspan; `append` requires adjacency and the same digest by type. |
| `Suffix digest start` | A bounded result plus verified length at its stop. `Done.suffix` needs independently checked extent; `Response.suffix?` uses it only if available. `Whole` is `Suffix digest 0`. |

`ExactAt` and `SuffixAt` state the semantics against a reference payload. `suffix_split`
proves the two directions between a suffix ending at `b` and exact `[a,b)` plus true
length `b`. An empty bounded range establishes only that the position is in bounds; an
empty suffix marks EOF exactly. An open-ended request beyond EOF is rejected, rather
than silently clamped. A range ending at EOF is not a suffix unless that end is
authenticated. `emptySuffix` converts checked extent to the zero-byte suffix there.

`Bounded.against` and `Suffix.against` compare against any *supplied* actually named
payload, returning a matching fact or an explicit low-256-bit compression collision.
Neither certificate asserts that some full payload exists behind opaque CVs. Appending
certificates compares both to the same reference; it does not manufacture a single
joint opening. No injectivity assumption is needed.

## Proof and wire boundary

- `SingleChunk.complete`: for any fully named payload of **0–1024 bytes**, any exact
  in-bounds bounded or open-ended request, and a cap large enough, the actual `Bao.encode`
  produces a combined, outboard, or slice frame accepted by the matching range API.
  The resulting bytes are exactly the requested projection and EOF is authenticated.
  The single-chunk outboard has only the length header; verification requires the
  separate original bytes. This is encoder-to-decoder completeness, not acceptance
  soundness alone.
- `Grouped.Cut.emit_checked` / `emit_named`: for every cut of an actually hashable
  canonical geometry, emitting raw groups, explicit forks, and opaque non-root
  siblings preserves the same checked CV/ROOT as full content. `Evidence.check_expand`
  identifies grouped evaluation with the explicit BLAKE3 opening. A collapsed subtree
  splits at its original byte geometry, retains the absolute 1 KiB counters, and uses
  the supplied ROOT flag at its top only. The proof covers unbalanced final subtrees.
  `forLayers k` can elide up to `k` bottom pair layers on fully selected subtrees,
  pruning unneeded branches and subdividing partial selections. `forLayers_reveals`
  proves that every selected chunk remains disclosed, and `raw_width` proves accepted
  raw groups supply their full original width. `k = 4` allows 16 KiB groups. An opaque
  sibling contributes a CV, but cannot expose bytes or prove EOF through that branch.
- The general cut theorem starts at typed evidence, **not wire serialization**. The
  multi-chunk combined/slice/outboard and raw Iroh paths have executable regressions;
  full encoder-to-wire-to-range completeness for those layouts is not proved here.

With the pinned toolchain, run:

```sh
lake build --wfail +Silmaril.Formats.Blake3Cas.RangeFacts.Thms \
  +Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk.Thms \
  +Silmaril.Formats.Blake3Cas.RangeFacts.Grouped.Thms +Silmaril.Formats.Iroh.Vectors
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/BaoRangeFacts.lean
```
