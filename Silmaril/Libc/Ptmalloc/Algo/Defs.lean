module

public import Silmaril.Libc.Ptmalloc.Heap.Thms

/-!
# ptmalloc: the algorithm model

A plain Lean model of ptmalloc over the abstract heap of `Silmaril.Libc.Ptmalloc.Heap`, parametric
in `C : Config`. No x86, no bytes: the algorithm-level theorems (well-formedness preserved,
refinement of the allocator institution) are proved once here, for every `C` with `C.Ok`.

## Structure

* `Abort`: glibc's `malloc_printerr` diagnostics (and an `internal` catch-all for states the
  model rules out). A well-formed state never aborts on a valid call (`Task.algo.noAbort`).
* **Leaf operations, defined here** from the component operations (`Tcache`, `Fastbins`, `Bins`,
  `Unsorted`, `Top`), each one glibc macro/inline helper, so that an x86 block that gcc inlined
  is matched against it by an outlining lemma: `tcacheGet`, `tcachePut`, `fastPush`, `fastPop`,
  `binPushFront`, `unsortedPush`, `binRemove`, `relabel`. A leaf touches only the components it
  names; its WF lemma uses `ArenaWF.withFast`/`withBins`/… (`Silmaril.Libc.Ptmalloc.Heap.Thms`).
* **Bodies** (`Ops`): the functions that run with the arena invariant owned (`_int_malloc`,
  `_int_free`, `_int_realloc`, `sysmalloc`, `systrim`, `malloc_consolidate`) and the thread-local
  `tcache_init`. They take and return a `Local` (one arena, one thread, shared, kernel); the
  `algo` builder defines `ptmalloc C : Ops C` in `Silmaril.Libc.Ptmalloc.Algo.Impl` and proves the
  obligations below for it.
* **Prologue/epilogue** (`malloc`, `free`, defined here from the bodies): `__libc_malloc`'s
  request check, the tcache fast path, the arena choice (`SINGLE_THREAD_P` shortcut or
  `arena_get` + the lock), the body, and the `errno` epilogue. Arena choice is a separate
  function (`Ops.arenaGet`) so the bodies never mention `main_arena`.

## Footprints

A body maps `Local → Local`; `World.put` writes back only the arena it locked, the calling
thread, the shared part and the kernel, so every other arena and thread is unchanged *by
construction*. Inside the `Local`, what a body may change is stated per obligation
(`Footprint`), never as a whole-state equality.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **glibc's diagnostics** (`malloc_printerr`), the ones the model can reach. -/
inductive Abort where
  | freeInvalidPointer
  | freeInvalidSize
  | doubleFreeTcache
  | doubleFreeFasttop
  | invalidNextSize
  | corruptedTopSize
  | corruptedDoubleLinked
  | unalignedTcache
  | unalignedFastbin
  | mallocMemoryCorruption
  | munmapInvalidPointer
  | mremapInvalidPointer
  /-- `double free or corruption (!prev)`: the chunk is already free (in a regular bin). -/
  | doubleFreePrev
  /-- `break adjusted to free malloc space` (`sysmalloc`). -/
  | breakAdjusted
  /-- `realloc(): invalid pointer` / `realloc(): invalid old size`. -/
  | reallocInvalid
  /-- A state the model's invariants exclude (no glibc message). -/
  | internal
  deriving DecidableEq, Repr

/-- A result of the model: an abort, or a value. -/
abbrev Res (α : Type) := Except Abort α

namespace Local

variable (C : Config)

/-! ## Leaf operations (one glibc macro or inline helper each, built from component operations) -/

/-- **`tcache_get (tc_idx)`**: pop the head of tcache bin `i`; the payload. Thread only. -/
def tcacheGet (l : Local) (i : Nat) : Option (Nat × Local) :=
  l.thread.tcache.bind fun tc =>
    (tc.get C i).map fun (p, tc') => (p, { l with thread := { l.thread with tcache := some tc' } })

/-- **`tcache_put (chunk, tc_idx)`**: push the chunk `(addr, size)` on tcache bin `i`. Thread
only. `none` without a tcache. -/
def tcachePut (l : Local) (c : Nat × Nat) (i : Nat) : Option Local :=
  l.thread.tcache.map fun tc => { l with thread := { l.thread with tcache := some (tc.put c i) } }

/-- Relabel the chunk at `a` of the arena's tiling. -/
def relabel (l : Local) (a : Nat) (u : Use) : Local :=
  { l with av := { l.av with tiles := l.av.tiles.relabel a u } }

/-- **Fastbin push** (`_int_free`'s fastbin path): components `Top` (relabel) and `Fastbins`. -/
def fastPush (l : Local) (a i : Nat) : Local :=
  { l with av := { l.av with tiles := l.av.tiles.relabel a (.fast i), fast := l.av.fast.push a i } }

/-- **Fastbin pop** (`_int_malloc`'s fastbin path): the head of fastbin `i`, lent out. -/
def fastPop (l : Local) (i : Nat) : Option (Nat × Local) :=
  (l.av.fast.pop i).map fun (a, fs) =>
    (a, { l with av := { l.av with tiles := l.av.tiles.relabel a .client, fast := fs } })

/-- **Small/large bin insert at the front, binmap marked** (components `Top`, `Bins`). -/
def binPushFront (l : Local) (a i : Nat) : Local :=
  { l with av := { l.av with tiles := l.av.tiles.relabel a (.bin i), bins := (l.av.bins.pushFront a i).mark i } }

/-- **Unsorted insert at the front** (components `Top`, `Unsorted`). -/
def unsortedPush (l : Local) (a : Nat) : Local :=
  { l with av := { l.av with tiles := l.av.tiles.relabel a (.bin 1), unsorted := l.av.unsorted.pushFront a } }

/-- **`unlink_chunk`** of `a` from small/large bin `i`, relabelled `u`. -/
def binRemove (l : Local) (a i : Nat) (u : Use) : Local :=
  { l with av := { l.av with tiles := l.av.tiles.relabel a u, bins := l.av.bins.remove a i } }

end Local

/-! ## Bodies -/

/-- **The bodies of ptmalloc** for one `Config`: the functions that run with an arena's invariant
owned (or, for `tcacheInit` and `ptmallocInit`, with the thread's/process's). Sizes are chunk
sizes (`nb`) unless named `n` (a request). The `algo` builder defines `ptmalloc C : Ops C` and
proves the obligations of this module for it. -/
structure Ops (C : Config) where
  /-- `ptmalloc_init` by thread `tid` (once per process; `__malloc_initialized`, `tcache_key`,
  tunables, `thread_arena = &main_arena` for the caller). -/
  ptmallocInit : World → Nat → Res World
  /-- `tcache_init` for thread `tid` (allocates the struct through `_int_malloc` of its arena,
  retrying through `arena_get_retry`). -/
  tcacheInit : World → Nat → Res World
  /-- **Prologue: the arena choice** for thread `tid` and request `nb` (`arena_get`: the
  `SINGLE_THREAD_P` shortcut takes `main_arena` without locking; otherwise `thread_arena` or a
  new/reused arena, then the lock). Returns the arena's address. -/
  arenaGet : World → Nat → Nat → Res (Nat × World)
  /-- `arena_get_retry` after a failed `_int_malloc` (multi-threaded only). -/
  arenaRetry : World → Nat → Nat → Nat → Res (Option Nat × World)
  /-- **`_int_malloc (av, n)`**: the payload address (0: refused). -/
  intMalloc : Local → Nat → Res (Nat × Local)
  /-- **`_int_free (av, p, have_lock)`** of chunk `p` (its tcache part included). -/
  intFree : Local → Nat → Res Local
  /-- **`_int_realloc (av, oldp, oldsize, nb)`**: the new payload (0: refused). -/
  intRealloc : Local → Nat → Nat → Nat → Res (Nat × Local)
  /-- **`sysmalloc (nb, av)`**: grow the heap (or `mmap` a chunk); the payload (0: refused). -/
  sysmalloc : Local → Nat → Res (Nat × Local)
  /-- **`systrim (pad, av)`** / `heap_trim`: give memory at the top back. -/
  systrim : Local → Nat → Res Local
  /-- **`malloc_consolidate (av)`**. -/
  consolidate : Local → Res Local
  /-- `munmap_chunk (p)` (no arena: `mmap`ed chunks are shared-part state). -/
  munmapChunk : Local → Nat → Res Local
  /-- `mremap_chunk (p, nb)` (0: refused). -/
  mremapChunk : Local → Nat → Nat → Res (Nat × Local)

namespace Ops

variable {C : Config} (A : Ops C)

/-- The body's view of `tid` at its current arena, after the prologue chose `a`. -/
def localAt (w : World) (tid a : Nat) : Res Local :=
  match w.local? tid a with
  | some l => .ok l
  | none => .error .internal

/-- Set thread `tid`'s `errno`. -/
def setErrno (w : World) (tid e : Nat) : World :=
  { w with threads := fun t => if t = tid then { w.threads t with errno := e } else w.threads t }

/-- `ptmalloc_init` unless done. -/
def init (w : World) (tid : Nat) : Res World :=
  if w.shared.init then .ok w else A.ptmallocInit w tid

/-- **An arena body with the prologue's arena choice and `arena_get_retry`** (`__libc_malloc`'s
and `__libc_calloc`'s shape): `SINGLE_THREAD_P` runs `body` on `main_arena` without locking and
without retry; otherwise `arena_get`, the body, and on failure (0) `arena_get_retry` and the body
again. -/
def withArena (w : World) (tid nb : Nat) (body : Local → Res (Nat × Local)) :
    Res (Nat × World) := do
  if w.single then
    let l ← localAt w tid w.mainArena
    let (p, l) ← body l
    return (p, w.put tid l)
  let (a, w) ← A.arenaGet w tid nb
  let l ← localAt w tid a
  let (p, l) ← body l
  let w := w.put tid l
  if p ≠ 0 then return (p, w)
  let (r, w) ← A.arenaRetry w tid a nb
  match r with
  | none => return (0, w)
  | some a' =>
    let l ← localAt w tid a'
    let (p, l) ← body l
    return (p, w.put tid l)

/-- **`__libc_malloc (n)`** (glibc 2.39): `ptmalloc_init`; `checked_request2size` (`ENOMEM`);
`MAYBE_INIT_TCACHE`; the **tcache path** (`tcache_get`, thread only); else `_int_malloc` on the
arena the prologue chose (`withArena`). -/
def malloc (w : World) (tid n : Nat) : Res (Nat × World) := do
  let w ← A.init w tid
  match C.checkedRequest2size n with
  | none => return (0, setErrno w tid 12)
  | some nb =>
    let w ← A.tcacheInit w tid
    let i := C.tidx nb
    let a0 := ((w.threads tid).arena).getD w.mainArena
    let l0 ← localAt w tid a0
    match (if i < C.tcacheBins then l0.tcacheGet C i else none) with
    | some (p, l) => return (p, w.put tid l)
    | none => A.withArena w tid nb fun l => A.intMalloc l n

/-- The arena of a heap chunk at `a` (`arena_for_chunk`): the arena whose chunks contain it. -/
def arenaOf (w : World) (a : Nat) : Option Nat :=
  w.arenaAddrs.find? fun x => ((w.arenas x).map fun av => av.chunks.any (·.addr = a)).getD false

/-- The `mmap`ed chunk at `c`, if any (`chunk_is_mmapped`). -/
def mmapped? (w : World) (c : Nat) : Option Chunk := w.shared.mm.chunks.find? (·.addr = c)

/-- **`__libc_free (p)`**: `free (NULL)`; an `mmap`ed chunk: the dynamic threshold (`raise`) and
`munmap_chunk`; otherwise `MAYBE_INIT_TCACHE` and `_int_free` on the chunk's arena (no lock
taken here: `_int_free` locks only for the merge path, which the model runs atomically). -/
def free (w : World) (tid p : Nat) : Res World := do
  if p = 0 then return w
  let c := p - C.hdr
  match mmapped? w c with
  | some ch =>
    let l ← localAt w tid w.mainArena
    let l := { l with shared := { l.shared with mm := l.shared.mm.raise C ch.size } }
    let l ← A.munmapChunk l c
    return w.put tid l
  | none =>
  let w ← A.tcacheInit w tid
  match arenaOf w c with
  | none => .error .freeInvalidPointer
  | some a =>
    let l ← localAt w tid a
    let l ← A.intFree l c
    return w.put tid l

/-- **`__libc_calloc (k, m)`** (glibc 2.39): `ENOMEM` when `k * m` overflows `ptrdiff_t`;
`ptmalloc_init`; `MAYBE_INIT_TCACHE`; `_int_malloc` on the chosen arena (calloc does **not** use
the tcache). Contents are not modelled, so the clearing is not visible here. -/
def calloc (w : World) (tid k m : Nat) : Res (Nat × World) := do
  if 2 ^ 63 ≤ k * m then return (0, setErrno w tid 12)
  let w ← A.init w tid
  let w ← A.tcacheInit w tid
  A.withArena w tid (C.request2size (k * m)) fun l => A.intMalloc l (k * m)

/-- **`__libc_realloc (p, n)`** (glibc 2.39, `REALLOC_ZERO_BYTES_FREES`): `realloc (p, 0)` frees;
`realloc (NULL, n)` is `malloc`; an `mmap`ed chunk: `mremap_chunk`, else keep it if it is big
enough, else `malloc`-copy-`munmap`; an arena chunk: `_int_realloc` (single-threaded: no retry;
otherwise on failure `malloc` elsewhere, copy, `_int_free`). -/
def realloc (w : World) (tid p n : Nat) : Res (Nat × World) := do
  let w ← A.init w tid
  if n = 0 ∧ p ≠ 0 then return (0, ← A.free w tid p)
  if p = 0 then return ← A.malloc w tid n
  let c := p - C.hdr
  match mmapped? w c with
  | some ch =>
    if c % C.align ≠ 0 ∨ 2 ^ 64 < c + ch.size then .error .reallocInvalid
    match C.checkedRequest2size n with
    | none => return (0, setErrno w tid 12)
    | some nb =>
      let l ← localAt w tid w.mainArena
      let (q, l) ← A.mremapChunk l c nb
      let w := w.put tid l
      if q ≠ 0 then return (q + C.hdr, w)
      if nb ≤ ch.size - C.sizeSz then return (p, w)
      let (q, w) ← A.malloc w tid n
      if q = 0 then return (0, w)
      let l ← localAt w tid w.mainArena
      let l ← A.munmapChunk l c
      return (q, w.put tid l)
  | none =>
  let w ← A.tcacheInit w tid
  match arenaOf w c with
  | none => .error .reallocInvalid
  | some a =>
    let l ← localAt w tid a
    let oldsize := l.av.tiles.sizeAt c
    if c % C.align ≠ 0 ∨ 2 ^ 64 < c + oldsize then .error .reallocInvalid
    match C.checkedRequest2size n with
    | none => return (0, setErrno w tid 12)
    | some nb =>
      let (q, l) ← A.intRealloc l c oldsize nb
      let w := w.put tid l
      if w.single ∨ q ≠ 0 then return (q, w)
      let (q, w) ← A.malloc w tid n
      if q = 0 then return (0, w)
      let l ← localAt w tid a
      let l ← A.intFree l c
      return (q, w.put tid l)

end Ops

/-! ## Obligations (owned by `algo`; stated for any `A : Ops C`, proved for `ptmalloc C`) -/

/-- The live set changes as a successful `malloc` of `n` bytes returning `p` says (`p = 0`:
unchanged up to permutation; else a fresh aligned payload of at least `n` bytes is added). -/
def MallocLive (C : Config) (n p : Nat) (live live' : List (Nat × Nat)) : Prop :=
  (p = 0 ∧ live'.Perm live) ∨
  (p ≠ 0 ∧ p % C.align = 0 ∧ ∃ u, n ≤ u ∧ live'.Perm ((p, u) :: live) ∧
    ∀ q ∈ live, q.1 + q.2 ≤ p ∨ p + u ≤ q.1)

/-- **Body footprint**: what a body may change in a `Local`. `arena`: the arena; `thread`: the
thread's tcache/errno; `shared`/`kernel`: `mp_`, the `mmap`ed chunks, the kernel. Everything
outside the `Local` is framed by `World.put`. -/
structure Footprint where
  arena : Bool := true
  thread : Bool := true
  shared : Bool := true
  kernel : Bool := true

/-- `l'` differs from `l` only inside the footprint `f`. -/
def Footprint.Within (f : Footprint) (l l' : Local) : Prop :=
  l'.avAddr = l.avAddr ∧ l'.isMain = l.isMain ∧
  (f.arena = false → l'.av = l.av) ∧ (f.thread = false → l'.thread = l.thread) ∧
  (f.shared = false → l'.shared = l.shared) ∧ (f.kernel = false → l'.kernel = l.kernel)

/-- **`Task.algo.leafTcacheGet`**: `tcache_get` keeps `LocalWF`, touches only the thread, and
moves one parked payload to the live set. (Leaf lemma; `algo` proves it, `x86sim` uses it.) -/
def Task.algo.leafTcacheGet : Prop :=
  ∀ (C : Config) (l l' : Local) (i p : Nat), C.Ok → LocalWF C l → l.tcacheGet C i = some (p, l') →
    LocalWF C l' ∧ Footprint.Within { arena := false, shared := false, kernel := false } l l' ∧
    ∃ u, ((l.thread.parked C).Perm ((p, u) :: l'.thread.parked C)) ∧ p % C.align = 0

/-- **`Task.algo.leafTcachePut`**: `tcache_put` of a lent-out chunk of the right size keeps
`LocalWF` when the bin has room, and touches only the thread. -/
def Task.algo.leafTcachePut : Prop :=
  ∀ (C : Config) (l l' : Local) (c : Nat × Nat) (i : Nat), C.Ok → LocalWF C l →
    i < C.tcacheBins → C.tidx c.2 = i → c.2 % C.align = 0 → C.minSize ≤ c.2 →
    c.1 ≠ 0 → c.1 % C.align = 0 →
    (∀ tc, l.thread.tcache = some tc → c ∉ tc.bins i ∧ (tc.bins i).length < C.tcacheCount) →
    l.tcachePut c i = some l' →
    LocalWF C l' ∧ Footprint.Within { arena := false, shared := false, kernel := false } l l'

/-- **`Task.algo.noAbort`**: on a well-formed view the bodies never abort on a valid call
(`_int_free` of a lent-out arena chunk not parked in this thread's tcache, any `_int_malloc`).
(Stated over `Local.arenaLive`: an `mmap`ed payload never reaches `_int_free`, and `_int_free`
of one would abort with `free(): invalid pointer`.) -/
def Task.algo.noAbort (C : Config) (A : Ops C) : Prop :=
  C.Ok → ∀ l, LocalWF C l →
    (∀ n, ∃ r, A.intMalloc l n = .ok r) ∧
    (∀ p u, (p, u) ∈ l.arenaLive C → ∃ l', A.intFree l (p - C.hdr) = .ok l')

/-- **`Task.algo.wfIntMalloc`**: `_int_malloc` keeps `LocalWF` and changes the view's live set as
`MallocLive` says (refinement of the institution's `malloc`, body level). -/
def Task.algo.wfIntMalloc (C : Config) (A : Ops C) : Prop :=
  C.Ok → ∀ l l' n p, LocalWF C l → A.intMalloc l n = .ok (p, l') →
    LocalWF C l' ∧ Footprint.Within {} l l' ∧ MallocLive C n p (l.live C) (l'.live C)

/-- **`Task.algo.wfIntFree`**: `_int_free` of a live payload `(p, u)` of the arena keeps
`LocalWF` and removes exactly it from the view's live set. (Over `Local.arenaLive`: with
`l.live`, a `LocalWF` view whose arena has a client chunk at the address of an `mmap`ed client
chunk of another size is a counterexample; `__libc_free` never sends `mmap`ed chunks here.) -/
def Task.algo.wfIntFree (C : Config) (A : Ops C) : Prop :=
  C.Ok → ∀ l l' p u, LocalWF C l → (p, u) ∈ l.arenaLive C → A.intFree l (p - C.hdr) = .ok l' →
    LocalWF C l' ∧ Footprint.Within {} l l' ∧ (l'.live C).Perm ((l.live C).erase (p, u))

/-- **`Task.algo.wfWorld`**: the world-level `malloc`/`free` keep `WorldWF` and refine the
institution's live-set contract (`World.live`). Follows from the body obligations, the leaf
lemmas and the frame of `World.put`, plus `ptmallocInit`/`tcacheInit`/`arenaGet` keeping
`WorldWF` and `World.live`. -/
def Task.algo.wfWorld (C : Config) (A : Ops C) : Prop :=
  C.Ok → ∀ w tid, WorldWF C w → tid ∈ w.tids →
    (∀ n p w', A.malloc w tid n = .ok (p, w') →
      WorldWF C w' ∧ MallocLive C n p (w.live C) (w'.live C)) ∧
    (∀ p u w', (p, u) ∈ w.live C → A.free w tid p = .ok w' →
      WorldWF C w' ∧ (w'.live C).Perm ((w.live C).erase (p, u)))

/-- **`Task.algo.mallocTotal`**: no abort at world level (with `wfWorld`, the refinement of the
institution's `malloc`/`free` is total). -/
def Task.algo.mallocTotal (C : Config) (A : Ops C) : Prop :=
  C.Ok → ∀ w tid, WorldWF C w → tid ∈ w.tids →
    (∀ n, ∃ r, A.malloc w tid n = .ok r) ∧ (∀ p u, (p, u) ∈ w.live C → ∃ w', A.free w tid p = .ok w')

end Silmaril.Libc.Ptmalloc
