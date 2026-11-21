# Read-through CAS cache refinement

Import `Silmaril.Semantics.Arena.Traits.Cache.Thms`. `Layer` adds a
positive byte cache to an existing backend. Every hot entry is pinned to
the exact bytes in the backend's authoritative observation. The cache is
not an independent byte authority and never stores a negative answer.

- `probe` is cache-only and an evicted or cold entry is `unavailable`.
  `get` is read-through: only the backing read can report authoritative
  absence. `warm` stages a hot entry only after a successful exact read;
  backing errors return no successor, and verified absence adds no entry.
- `withCache_refines` implements the same `CasArena` interface observed
  through the backing state. Plain edits leave authoritative bytes alone;
  successful put/attach extends the byte graph. `Layer.advance` preserves
  hot reads only with this inclusion witness, not based on matching names
  or an equality of store labels. Switch authorities using `cold`.
- `evict` clears only the hot copy. With a readable backing, `evict_get_exact`
  proves equality of read-through answers before and after eviction. With an
  unavailable backing, eviction may convert a hit to an error; it never
  converts that failure into verified absence. A collision still returns
  no successor and preserves the old binding.

This layer concerns bytes. It does not evict the user-visible parsed slots,
reclaim public handles, delete authoritative data, authenticate arbitrary I/O,
or prove a persistent transaction. Read-through proof reuse is separate from
parsed block provenance and rooted retention. An in-memory backing can use
an authoritative name-to-bytes table. A layered blob-key or SQLite backing
needs evidence that a present index with unavailable blob bytes is not
reported absent, and that index and content changes commit atomically.

```sh
lake build --wfail +Silmaril.Semantics.Arena.Traits.Cache.Examples
make check CHECK_TARGETS='+Silmaril.Semantics.Arena.Traits.Cache.Examples'
```
