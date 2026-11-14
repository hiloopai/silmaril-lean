# Kernel-friendly finite maps and sets

Finite maps and sets that the Lean kernel evaluates quickly under `decide +kernel`
or `rfl`, with proofs of their extensional semantics. They live in the `Data` tree
and import only Lean core (`Init`), so they can be used from any region.

| Structure | Keys → values | Status | Modules |
| --- | --- | --- | --- |
| `BytesMap α` | `List UInt8 → Option α` | implemented, proved | `Silmaril.Data.BytesTrie.{Defs,Thms,Tests}` |
| `NatRangeMap α` | `Nat → Option α`, by runs | implemented, proved | `Silmaril.Data.NatRangeMap.{Defs,Thms,Tests}` |
| `NatBitSet` | `Nat → Bool`, one bit mask | implemented, proved | `Silmaril.Data.NatBitSet.{Defs,Thms,Tests}` |
| `StringMap α`, `IntRangeMap α`, `BytesSet`, nibble tries, shared trees | | API design only (below) | — |

## What is proved

Each structure has a *raw* representation, whose lookup function is its
semantics, and a *canonical* subset. The theorems relate the two:

1. **Specification.** Each operation is specified pointwise by lookups: for
   example, `BytesTrie.find?_alter` says that `(t.alter ks f).find? js` is
   `if js = ks then f (t.find? ks) else t.find? js`. For `BytesTrie`, this needs
   only `WF`: siblings sorted.
2. **Canonical form is preserved.** `canon_alter`: `alter`, `insert` and `erase`
   map canonical tries to canonical tries (they keep siblings sorted and prune
   value-free nodes).
3. **Uniqueness.** `BytesTrie.eq_of_find?_eq`: two *canonical* tries with the same
   lookups are equal. Raw tries are **not** unique. The same map can be stored
   with unsorted or duplicate siblings or with value-free nodes;
   `BytesMap.Tests` gives an example. The isomorphism is with the canonical
   subtype `BytesMap α`, not with raw tries; `BytesTrie.Equiv` is the extensional
   equivalence on raw tries.
4. **Completeness.** `BytesMap.exists_of_finite`: every finitely supported
   function `List UInt8 → Option α` is the lookup of a map. Together with
   `BytesMap.ext_iff`, `find?` is a bijection from `BytesMap α` onto the finitely
   supported functions.
5. **Decidable equality** is structural on the canonical form. It goes through a
   `Bool` comparison (`Trie.beq`, `beq_iff`), because the kernel evaluates a derived
   `DecidableEq` instance about 4× slower (measured: 3.8 s against under 0.1 s on top
   of the 1.8 s needed to build two 300-entry tries).
6. **Certificate validation.** `BytesMap.ofCanonB t` accepts a raw trie (for
   example a literal produced by a tool) once the kernel evaluates `t.canonB = true`;
   `canonB_iff` proves the check equivalent to `Canon`.

`NatBitSet` stores the set in a single `Nat`, so it is canonical by construction
(`ext_iff` uses `Nat.eq_of_testBit_eq`). Its operations are the kernel's
GMP-accelerated `|||`, `&&&`, `^^^` and `2 ^ k`.

## BytesTrie representation

```lean
inductive Trie (α) | nil | node (b : UInt8) (v : Option α) (child next : Trie α)
structure BytesTrie (α) where root : Option α; kids : Trie α
def BytesMap (α) := { t : BytesTrie α // t.Canon }
```

The trie uses the left-child right-sibling encoding of a 256-ary trie. It is an
ordinary inductive, not a nested one, so every operation is structural
recursion: no well-founded recursion blocks kernel reduction, and the proofs are
plain inductions. Every node stores the byte on its edge, the value at the end
of that edge, its first child and its next sibling. `Canon` means:

- siblings are strictly increasing by byte;
- every node holds a value or has a child.

The canonical tries are exactly the reachable normal forms.

## NatRangeMap representation

```lean
structure Run (α) where gap : Nat; len1 : Nat; val : α   -- [start+gap, start+gap+len1]
abbrev Raw α := List (Run α)
structure NatRangeMap (α) where raw : Raw α; canonical : Raw.Canonical raw
```

Runs are stored in relative coordinates: each run starts `gap` after the end of
the previous run and covers `len1 + 1` keys. Sorted, disjoint and non-empty
runs therefore hold *by construction*. The only canonical-form condition is
maximality: no run with gap 0 has the same value as its predecessor.

- `Raw.find?_assign` and `Raw.find?_erase` hold for every raw list.
- `canonical_assign` and `canonical_erase`: `assign` and `erase` merge only where
  they touch and share the runs above the changed range.
- Uniqueness of canonical forms is `Raw.eq_of_find?`, completeness is
  `NatRangeMap.complete`, and extensionality is `NatRangeMap.ext_iff`.
- `normalize` merges a non-canonical raw list into canonical form
  (`find?_normalize`, `canonical_normalize`).

The raw layer is its own header pair (`NatRangeMap.Runs.{Defs,Thms}`), because
the map operations need the canonicity proofs.

## Measurements

`scripts/bench/finmap-kernel.py` generates one Lean file per scenario and checks
it with `lake env lean`. `#kernel_time p` builds the term that `decide +kernel`
would build and times `addDecl`, which is the kernel check. A warm-up
declaration comes first, and `Elab.async` is off. The *materialized* scenarios
first evaluate the map at elaboration time with the compiler, then splice its
normal form in as a literal term (`materialize%`). This simulates a map shipped
as a certificate.

Keys are `n` three-byte strings:

- *dense*: `i` in big-endian order, up to 256 siblings per level;
- *spread*: a multiplicative hash of `i`.

The assoc-list baseline is `List (List UInt8 × Nat)` with `List.lookup`. Its
*first* key is at the end of the list and its *last* key at the head.

Machine: 2-vCPU gVisor sandbox, Lean `nightly-2026-11-05`. These are single runs;
repeated runs of the same file varied by about 5 %. Raw data comes from
`scripts/bench/finmap-kernel.py --out finmap-kernel.json`. Times in ms:

| scenario (ms, kernel) | dense 100 | dense 1000 | dense 4000 | spread 100 | spread 1000 | spread 4000 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| build+lookup | 539 | 3,601 | 6,929 | 176 | 10,246 | 71,383 |
| build+lookup(assoc) | 27.1 | 206 | 1,103 | 16.2 | 166 | 828 |
| lookup first(materialized) | 0.8 | 2.6 | 1.1 | 1.1 | 0.8 | 1.0 |
| lookup last(materialized) | 7.0 | 13.7 | 17.0 | 3.7 | 7.5 | 13.6 |
| lookup first(materialized assoc) | 16.6 | 125 | 534 | 11.8 | 87.1 | 378 |
| lookup last(materialized assoc) | 1.0 | 3.6 | 1.3 | 1.4 | 1.2 | 1.5 |
| insert+lookup(materialized) | 16.5 | 29.2 | 23.1 | 10.3 | 24.3 | 42.2 |
| erase+lookup other(materialized) | 1.3 | 1.1 | 1.7 | 1.0 | 1.3 | 1.2 |
| validate canonB(materialized) | 7.4 | 53.4 | 233 | 19.1 | 161 | 549 |
| equality(materialized) | 10.6 | 87.5 | 537 | 22.4 | 185 | 735 |
| equality(build vs buildRev) | 521 | 14,964 | 96,175 | 557 | 34,932 | 188,359 |

`NatBitSet` (multiples of 3, built by `n` inserts in the kernel; ms):

| scenario | n = 1000 | n = 10000 | n = 100000 |
| --- | ---: | ---: | ---: |
| build+mem | 48.2 | 829 | 16,114 |
| build+equality | 107 | 1,916 | 31,846 |

`NatRangeMap` was measured separately by wall-clock difference against a base
file. Its map is a literal canonical map of `N` runs; each operation was
repeated three times, giving about ±50 ms of noise; times in ms:

| operation | N = 100 | N = 1000 | N = 5000 |
| --- | ---: | ---: | ---: |
| lookup, last key | ~0 | 59 | 327 |
| assign at end + lookup | 19 | 433 | 7,209 |
| assign at front + lookup at end | ~0 | 58 | 320 |
| erase in middle + lookup at end | 10 | 155 | 944 |
| `m = ofList m.toList` | 30 | 479 | 3,093 |
| top-down build + lookup at end | 21 | 322 | 2,285 |

Run lists are linear: about 50–120 µs per run traversed. Appending at the end
is O(n²) (400 appends: 31 s), so build top-down or with `ofList`. `assign` at the
end grows faster than linearly between 1000 and 5000 runs; the cause has not been
found. Use `decide +kernel`: plain `decide` exceeds `maxRecDepth` at 200 runs.

### Reading the numbers

- **Kernel reduction costs roughly 30–50 µs per sibling comparison**: measured by a
  micro-benchmark scanning 256 literals, 9–14 ms per scan. Lookup cost is
  therefore the number of siblings scanned, at most 256 per byte in this
  encoding, plus a constant.
- **Materialized lookup is flat in `n`**, at a few ms in the worst case. Assoc
  lists are linear in the position of the key.
- **Updating a materialized map is cheap and persistent.** `insert` copies only
  the path to the key, and the rest of the literal is shared by pointer. A
  lookup after an insert costs about as much as a lookup, not a rebuild.
- **Computing a trie inside the kernel is expensive** (`build+lookup`): 7–90×
  slower than building an assoc list by consing, which does no comparisons.
  Each `insert` scans sorted siblings, up to 256 wide, and the kernel does not
  memoize the fold. Building thousands of entries costs seconds; 4000 spread
  keys take 71 s. The trie pays off when the map is a literal or a definition
  checked once: lookup is then flat, and equality is canonical. It does not pay
  off when a proof rebuilds the map inside every `decide`.
- **Equality** of canonical maps is a structural walk: linear in size, and cheap
  on literals. Comparing two maps *built in the kernel* is dominated by forcing
  both builds completely.
- **`canonB` validation** of a literal costs about one full walk, comparable to
  equality.

## Design for the rest (not implemented)

**Bounded-width shared object trees.** The left-child right-sibling encoding
scans up to 256 siblings per byte. A 16-ary *nibble* trie with a fixed-arity
constructor (`node16 v c0 … c15`) takes two O(1) projections per byte, at the
cost of 16 fields per node. A binary trie takes eight steps per byte, with no
scanning and with tiny nodes. The canonical-form argument carries over
unchanged: prune empty nodes, and use positional children instead of sorted
siblings, which removes the sortedness invariant entirely. The same
`Equiv`/`Canon`/uniqueness interface would apply. Kernel terms already share
untouched subtrees by pointer; to share *across declarations*, a tool can emit
repeated subtrees as named constants. The kernel then checks each constant once,
and `rfl` equality short-circuits on identical constants. `decide` through `beq`
does not short-circuit, so it still walks shared subtrees.

**Leaf certificate validation.** Generalize `ofCanonB` with a per-leaf `Bool`
checker `check : α → Bool`. A map whose leaves carry claims, such as symbol
addresses, is accepted after one kernel walk of `canonB && allLeaves check`. The
soundness lemma is `allLeaves check t = true → ∀ ks a, t.find? ks = some a → check a = true`.

**Logical encodings.** Because `find?` is a bijection onto finitely supported
functions, a canonical map can be translated into any logic with finite maps
(SMT arrays with a default value, HOL finite maps) and back. A digest of the
canonical serialization, computed for example with the Crypto region's hashes,
then identifies the map. Merkle-style per-node digests would give incremental
membership proofs.

**`StringMap α` with Unicode semantics.** Use `BytesMap α` keyed by
`String.toUTF8`. Keys are sequences of Unicode scalar values. There is no
normalization: NFC and NFD forms are different keys. UTF-8 byte order is code
point order, so `toList` is sorted by code points. Uniqueness needs the
invariant that every stored byte key is valid UTF-8; this holds when keys only
enter through `String`. Prefix queries agree with string prefixes only at
character boundaries. Open: the kernel cost of `String.toUTF8` on literals has
not been measured.

**`IntRangeMap α`.** Use a pair of `NatRangeMap α`: non-negative keys `k`, and
negative keys `-k-1`. A range that crosses zero splits deterministically, so
canonical forms stay unique.

**Sets.** `BytesSet := BytesMap Unit` and `NatRangeSet := NatRangeMap Unit`
inherit all theorems. Use `NatBitSet` for dense sets of small naturals: its mask
has `max + 1` bits.

## Not covered

No union or merge of tries, no ordered range queries, no `toList` correctness
theorem, and no nibble or binary trie implementation. `IntRangeMap` and
`StringMap` are designs only, and `Data` is not yet listed in `regions.toml`.
Symbol tables (ELF) and memory overlays (Wasm) are expected clients and are
being developed separately.

## Build

```sh
lake build --wfail Silmaril.Data.BytesTrie.Tests Silmaril.Data.NatRangeMap.Tests \
  Silmaril.Data.NatBitSet.Tests
scripts/bench/finmap-kernel.py --sizes 100,1000,4000 --out finmap-kernel.json
```
