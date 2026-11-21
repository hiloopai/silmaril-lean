# BLAKE3 observation extension

The [abstract range kernel](blake3-range-kernel.md) checks a byte interval against
a digest and claimed extent. The [wire integration](blake3-wire-cas.md) keeps
that claim separate from checked EOF, trusted extent, and frame completion.
This development addresses a different question: can *all* observations hold
in one model, including at digests for which no whole is named yet?

## Closed observations and naming models

[`Fact`](../../Silmaril/Semantics/Naming/ByteRange/Extension/Defs.lean) is the
minimal local semantics: an exact range at an offset (`Slice`), an exact whole,
or an exact end. A range of zero bytes still has its offset as a lower bound;
it does not assert EOF. A whole contributes all its bytes and its length. An
EOF contributes length but no bytes. `Observations` is a predicate on names and
facts, not a finite list or a set tied to a single claimed length.

[`Observations.exists_model_iff`](../../Silmaril/Semantics/Naming/ByteRange/Extension/Thms.lean)
requires exactly:

1. The old relation is binding, and every old payload already satisfies all
   facts about its name. The extension leaves each old fiber exactly as it was.
2. Per queried name, all observations of any byte agree, the endpoints have a
   common finite upper bound, and every observed end accommodates every fact.
   In particular, two explicit end facts must agree; a range cannot go past one.

The construction chooses one representative at each fresh queried name. It
chooses the explicit length when present, or a finite bound otherwise, and
fills uncovered positions with zero. `fits_filling` lets the caller supply any
gap bytes at an admissible length. No new unqueried names are introduced.
The representative is unique **in the chosen relation**, not necessarily
forced by the observations. The construction is logical, not an executable
store or a hash preimage algorithm. There is no global bound shared across
names; arbitrarily many observations may be supplied. Unbounded endpoints at
one name are impossible for finite `Bytes`, even if the values on every
overlap agree. Kernel-certified endpoints already have a common bound of
`2^64 - 1`; that does not establish byte agreement or compatibility with EOF.

If the relation must additionally satisfy `UniqueNames` (one name per payload),
`exists_unique_model_iff` gives the extra exact condition: base canonicality
and an injective choice of fresh representatives avoiding all existing
payloads. For example, two different fresh names asserting the same whole
have a binding model but cannot satisfy this extra condition.

## Compression realizability

[`Compression.WitnessFamily.union`](../../Silmaril/Crypto/Blake3/Range/Extension/Thms.lean)
glues local witnesses for the queried digests. Each support must legally name
its chosen compatible whole, agree with the base table, and agree pairwise
(including with itself): same input implies same output, and same output
implies same input. The union is a canonical collision-free extension, even
for arbitrary witness families. `Compression.exists_extension_iff` is the
corresponding characterization. A global realization also induces a binding
naming model via `Compression.Realizes.model`. `Named.uniqueNames` gives its
opposite-direction uniqueness under canonical compression.

These hypotheses are checked on actual whole traces, not just on the entries
seen while checking partial proofs. An opaque CV has no existential preimage
obligation in `Trace`. Consequently, neither agreement of the observed byte
facts nor collision-freedom of the current table suffices for realizability.

## What the checker alone cannot imply

The two [counterexample theorems](../../Silmaril/Crypto/Blake3/Range/Extension/Counterexample/Thms.lean)
use the same 19-row, canonical and collision-free abstract compression table.
Lean evaluates the existing `verifyRangeWithEOF?` and `verifyRange?` to certify
the following results (the table is not the concrete BLAKE3 compression
function):

| Claimed extent | Path to byte 1024 | Accepted byte | Verified EOF |
| --- | --- | --- | --- |
| 1025 | right | `1` | yes |
| 2049 | left, then right | `0` | not supplied |

- **Opaque preimage obstruction:** In the first opening the left CV is opaque,
  but its only allowed preimage in a collision-free extension is a non-ROOT
  parent input. Verified EOF forces length 1025 for any named whole. Its left
  subtree is necessarily a full chunk at counter 0; the final chunk flags
  cannot equal the parent flag. Thus even the first opening plus EOF can have
  an abstract binding model (with arbitrary bytes in the gap) but no
  collision-free compression extension that names a whole at its digest.
- **Cross-extent conflict:** The two traces use the same ordered root children.
  The shorter trace exposes the right child and hides the left. The longer
  trace opens the left and hides the right. Both disclosed chunks have absolute
  counter 1, but their different paths impose no common child input. The range
  facts conflict at byte 1024, even if neither claimed extent is retained as an
  observation. Comparing matched parent inputs, flags, counters and final
  blocks does not force agreement between these unmatched paths.

[`CertifiedAt.model`](../../Silmaril/Crypto/Blake3/Range/Extension/Thms.lean)
gives a sufficient guard directly over checker evidence: for each queried
digest, use one common geometry for all its observations, and require any
already-named payload at that digest to match that extent. With matched
geometry the two reads route each common byte through the same path. The
`Agree` trace comparison ensures that two disclosed bytes there agree; an
opaque branch cannot supply a read. Whole and EOF facts impose their actual
length, not an arbitrary range header. This guard is sufficient, not necessary.

## Integration boundary and verification

Translate an exact kernel `Checked` to `Certified` by existentially retaining
its claim, a whole via `Named`, and checked EOF via `CheckedEOF`. For a trusted
extent or checked EOF, use `CertifiedAt` when the corresponding range evidence
is at that extent. A later open/closed observation API can translate exact
closed ranges to `Fact.range` and proven ends to `Fact.eof`. No translation
from a raw header, parser completion, or an unclosed request is asserted. No
new Bao/Iroh completeness, wire release, runtime, or Rust theorem is needed.

This development now targets `main` after [#1600's dedicated merge `85677c63`](https://github.com/hiloopai/silmaril-lean/commit/85677c639a1c668c9671bf4547343a2881a853b5).
The integration patch was originally reviewed at
[`fad3de005`](https://github.com/hiloopai/silmaril-lean/commit/fad3de0054acc7f55aab0aaa8eece5d684d0db17)
and rebased after [#1583](https://github.com/hiloopai/silmaril-lean/pull/1583),
[#1586](https://github.com/hiloopai/silmaril-lean/pull/1586), and
[#1587](https://github.com/hiloopai/silmaril-lean/pull/1587) landed. Only the
observation-extension commit is new in [#1617](https://github.com/hiloopai/silmaril-lean/pull/1617).

```sh
lake build --wfail +Silmaril.Crypto.Blake3.Range.Extension.Counterexample.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/crypto/Blake3ObservationExtension.lean
scripts/check-layout.sh
```
