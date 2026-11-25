# Decoder graphs and machine rebasing

[`Parse.DecodeGraph`](../../Silmaril/Parse/DecodeGraph/Defs.lean) is a
success-only interface parameterized by the byte representation. A query
contains a semantic `context`, a `bytes` buffer, and a window `[pos, stop)`.
An outcome `(value, endPos)` identifies the consumed segment `[pos, endPos)`
and the remainder of the window. Cursors index the buffer; mode, architectural
PC and other semantic inputs belong in the context. `successes` projects the
successful outcomes of the existing `ByteParse.Res`; diagnostic failures aren't
merged, nor equated with architectural faults.

## Byte representations and parser contracts

The generic graph uses `List UInt8` as its reference carrier and does not
import `ByteParse` or Wasm. The optional
[`ByteParse` bridge](../../Silmaril/Parse/DecodeGraph/ByteParse/Thms.lean)
uses the existing cursor parser, diagnostics, byte-list grammar carrier,
segment and contracts without changing `ByteParse.Defs` or its callers.
`ofGrammar` interprets the grammar at a reference cursor. `overView` compares
other representations against that view without computing the reference list
on the executable path. `SoundFor` and
`CompleteFor` are directed comparisons at valid windows; a deterministic
implementation can cover all specified successes only if they agree there.
For `ByteArray`, these contracts are equivalent to `ByteParse.Sound` and
`ByteParse.Complete` on a context-free parser. `Unit` is the canonical
context-free case; ignoring an inhabited context preserves and reflects graph
inclusion.

[`kbyte`](../../Silmaril/Parse/DecodeGraph/KBytes/Defs.lean) uses
`KBytes.get?` directly. Under `wf`, it agrees with `ByteParse.byte` at the
same cursor and stop, including EOF. The
[checked examples](../../Silmaril/Proofs/Parse/DecodeGraph/Examples.lean)
also establish exact agreement with the singleton-byte grammar at valid
windows and read `c3` across a rope node at nonzero position, then stop before
`cc`. This uses the existing `KBytes.get?_eq` representation law. `readLE`
and `slice` already have their own `toList` laws; the ELF staged reader uses
`readLE` with a directed `sub_kbytes` proof. `ChunkView` exposes whole chunks
as lists for incremental acceptance; it is not a cursor accessor. No new
byte helpers or throughput claims are needed for this check.

Plain parsers may succeed with zero consumption (`pure_zero_success`). A
`ByteParse.NonEmpty` grammar gives strictly positive reference successes;
the block builder requires progress at each step. A positive-only graph
could instead store a `PNat` width (`Nat.succPNat` and `PNat.natPred` in
Mathlib are inverses), or index its end by `pos < endPos`. At a fixed entry these
encode the same positive spans by adding the width and subtracting the
entry. They would complicate the shared zero-capable outcome space and
cross-graph transport. An interop lemma is deferred until a client needs
positive widths as values.

## Order and composition

- The ambient complete lattice is Mathlib's `SetRel` (a set of pairs): join is
  union and meet is intersection. Bounds, positive consumption, prefix
  locality, determinism and completeness relative to a specified relation are
  independent contracts. `not_deterministic_sup` shows that different successful
  results at the same query survive a join, even when each decoder on its own
  is deterministic. This includes disagreement on length alone.
- `transport` postcomposes with an arbitrary relation on values while keeping
  the consumed span; `map` specializes it to a function. `pointwise` lifts an
  instruction relation via `List.Forall₂`, with an append law. A relation on
  **whole lists** uses the same transport and composition, without any
  equal-length or append assumption. If independent chunks do not agree on an
  intermediate segmentation, a chunk-wise composition rule cannot be inferred
  from ordinary relational composition.
- Types and relations have identities and associative composition. A directed
  comparison `R ⊆ R'` is a 2-cell between parallel relations with the same
  input and output types. `rebase_mono` composes two such comparisons
  horizontally: `A ⊆ A'` and `M ⊆ M'` give `A ○ M ⊆ A' ○ M'`.
  `rebase_interchange` checks that horizontally composing the vertical chains
  gives the same inclusion as vertically composing the horizontal pairs.
  These are checked concrete Lean laws, not a bundled Mathlib 2-category
  instance: horizontal composition uses Mathlib's `SetRel.comp_subset_comp`
  and interchange uses proof irrelevance of inclusions. For a fixed query
  context, the laws make graph
  transport covariant and observed-machine rebasing contravariant on arrows
  (and both monotone on 2-cells), taking graphs into their inclusion posets. A
  sound map from one decoder to another is the inclusion of the transported
  graph in the target graph; identities and composites follow from those same
  laws. No second category hierarchy is introduced.

## Entry, exit and observations

[`Machine.DecodeGraph.blocks`](../../Silmaril/Machine/DecodeGraph/Defs.lean)
is a bounded witness, not an executable parser or CFG. The caller supplies an
entry cursor, window and terminator predicate independent of semantic
execution. `Path` requires positive, in-window consumption at every instruction,
advances only the cursor, and closes at the first terminator on that path.
The exit *byte boundary* is not the successor PC. No synthetic
terminator, resynchronization, partial block, or empty block is emitted for a
truncated, undecodable, or fuel-exhausted path. End-of-input is not itself a
terminator, unlike the straight-line `Decoder.decodeAll` policy. A valid block
may leave a nonempty suffix. `path_bounds` checks nonemptiness, fuel and byte
bounds; `blocks_deterministic` lifts determinism through a fixed boundary
policy. `IsBasicBlock Context Source Block` independently checks or assembles
the listing into an actual block type, possibly with a contextual typing
side condition. Its context-free form ignores the context. The example also
translates to `Source ⊕ Terminator` tokens and assembles a `TerminatedBlock`
record, giving the final transfer its own field and excluding earlier exit
tokens. No typing or semantic execution theorem follows just from this shape.

`rebase adapter model` pulls back an observed execution relation on a common
base. Comparing two models by observation inclusion on that base implies
inclusion after rebasing along the same adapter, and successive rebases compose.
An input with no witness has no observations (so inclusion can be vacuous).
`dom_rebase_of_covered` gives exact availability on the adapter domain when
every possible witness admits some observation. Multiple witnesses contribute
the union of their observations; acceptance by some witness is not a must
guarantee. For an ambiguity-independent answer require agreement of the
observation sets at all related base inputs, or an independently justified
unique witness. To use an existing [`Behaviour.Semantics`](../../Silmaril/Machine/Behaviour/Semantics.lean),
take its `Beh` as the observation relation: labeled divergence, UB or faults
are copied unchanged along a witness, but the construction neither creates
these labels from decode failure nor proves that execution on bytes has the
same behaviors. It does not turn whole blocks into small-step semantics.

The [checked x86 example](../../Silmaril/Proofs/Machine/DecodeGraph/X86Example.lean)
uses the existing `X86.Insn.byteDecoder`. At entry 16, `41 50 c3 cc` decodes as
`push r8; ret`, consumes three bytes and leaves `cc`. A truncated `41` has no
block. The toy semantics counts ordinary instructions and observes a return
tag; it does not execute a real push, access the stack, or compute a return
address. Its two-instruction listing relates to a singleton abstract block;
the checked rebases admit the observation at both list and byte inputs.
Rebasing the typed block machine also gives that observation directly from the
assembled block record.

## Directed comparison with the executable decoder

The [`Machine.Decoder` adapter](../../Silmaril/Machine/DecodeGraph/Decoder/Thms.lean)
converts only the queried reference window from `UInt8` to `BitVec 8`.
`ofDecoder_exact` identifies the single-instruction graph with the grammar of
segments the existing decoder consumes exactly. `blocks_subset_sequentialPrefixes`
proves a directed comparison for **all** contexts, reference buffers, fuel and
successful factored block results. On the exact consumed window prefix, the unchanged
`Decoder.decodeBlock` returns a listing with the same instructions after
erasing its offsets. The proof uses prefix locality and the executable's
recursive decode, not equality by wrapping the same implementation.

The x86 example checks the direction is strict: the sequential decoder also accepts
the two-byte `push r8` prefix with no terminator, which the factored decoder
rejects. On the three-byte prefix the sequential decoder computes the listing at
offsets 16 and 18; on the full sample with extra fuel it fails at `cc`. Thus the
claim compares successful consumed prefixes, not equal behavior on the full
stream or preservation of failure diagnostics. `stack_byte_observations_refine`
then composes the adapter inclusion with the listing projection and the toy
block machine, proving observation inclusion at byte inputs.

## Atomic decoder institution

[`Institution`](../../Silmaril/Parse/DecodeGraph/Institution/Thms.lean)
checks the atom-only institution separately from forward transport. Fix the
context type, byte representation and cursor carriers. A signature is an instruction
type, a signature arrow is a function, and a sentence asserts that one exact
query, instruction and end cursor is successful. `translate` maps
only the instruction. Models are relational success graphs (with only
identity model morphisms), and `reduct` is inverse image: an exact source
success holds precisely when its translated target success holds. The
sentence maps and contravariant reduct satisfy identity and composition, and
the atomic satisfaction condition is definitional. No functor bundling or
logical connectives are needed for this fragment.

This is not a construction on deterministic executable decoders. If two
distinct source instructions map to a successful target instruction, the
reduct has both as successes at the same input and span, even if the target
graph was deterministic (`reduct_not_deterministic_of_collision`). Forward
`map` takes images of successes; reduct admits all preimages. Neither runs a
decoder or preserves diagnostics.

## Staged gaps

- No production CFG or fetch bridge in this layer. A consumed-prefix listing
  can later connect to `Region.decode?_fetch` when that prefix is loaded at a
  chosen architectural address with execute permission. Whole-region listings
  can scan past a transfer; `Decoded.edges` and `listing_sound` need address,
  state coverage and invariant hypotheses that a cursor proof does not supply.
- No parser/representation benchmark, direct rope-backed x86 decode, or
  comparison of allocation or throughput. The rope check is for one byte;
  broader measurements should compare equivalent window workloads and exclude
  reference conversion from the measured parser path.
- Factoring a stand-alone executable parser core out of the widely imported
  `ByteParse.Defs` is separate work. The graph and machine adapters do not
  depend on that extraction.
- Logical fragments beyond atoms and signature arrows beyond functions are
  not part of this institution experiment. In particular, determinism and
  negative or universal properties under arbitrary relations do not follow
  from covariant success transport.

Targeted check:

```sh
lake build --wfail Silmaril.Parse.DecodeGraph.Institution.Thms \
  Silmaril.Proofs.Parse.DecodeGraph.Examples Silmaril.Proofs.Machine.DecodeGraph.X86Example
```
