module

public import Silmaril.Libc.Ptmalloc.Algo.Malloc.Defs

/-!
# ptmalloc algorithm: initialisation and the arena choice (world level)

* `ptmallocInit` (`ptmalloc_init`): `__malloc_initialized`, `tcache_key` (`getrandom`, else
  `random_bits`: both kernel answers), `thread_arena = &main_arena` for the caller.
* `arenaGet` (`arena_get`): `thread_arena`, else `arena_get2`; `arenaRetry` (`arena_get_retry`):
  `main_arena` after a non-main arena failed, else `arena_get2` avoiding `main_arena`.
* `arena_get2` (`arenaGet2`): the head of `free_list`, else a new arena (`_int_new_arena`, a new
  heap with the `malloc_state` after its `heap_info`) while `narenas ≤ arena_test`, else reuse.
  **Model gap (documented, multi-threaded only):** `narenas_limit` from the CPU count and
  `reused_arena`'s round robin over the arena list are simplified to reusing `main_arena`.
* `tcacheInit` (`tcache_init`): unless shutting down, `arena_get`, `_int_malloc` of
  `sizeof (tcache_perthread_struct)` (= `tcache_bins * (count width + 8)`), retry through
  `arena_get_retry`; the chunk becomes the thread's (empty) tcache, labelled `internal`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- **`ptmalloc_init`** by thread `tid`. -/
def ptmallocInit (w : World) (tid : Nat) : Res World :=
  let (a, k) := w.kernel.ask
  let (key, k) := match a with
    | .ok v => (v, k)
    | .refuse => match k.ask with
      | (.ok v, k) => (v, k)
      | (.refuse, k) => (0, k)
  .ok { w with
    shared := { w.shared with init := true, key }
    kernel := k
    threads := fun t => if t = tid then { w.threads t with arena := some w.mainArena } else w.threads t }

/-- Set thread `tid`'s `thread_arena`. -/
def setArena (w : World) (tid a : Nat) : World :=
  { w with threads := fun t => if t = tid then { w.threads t with arena := some a } else w.threads t }

/-- `new_heap (sz)`: reserve a `HEAP_MAX_SIZE`-aligned heap of `sz` bytes (`none` when `sz` is too
large or the kernel refuses). -/
def heapAttempt (w : World) (sz : Nat) : Option (Nat × Nat) × World :=
  if C.heapMaxSize < sz then (none, w) else
  match w.kernel.mmap C.heapMaxSize C.heapMaxSize with
  | (none, k) => (none, { w with kernel := k })
  | (some h, k) => (some (h, sz), { w with kernel := k })

/-- **`_int_new_arena (size)`**: a new heap (with `top_pad`, else without), the arena struct after
its `heap_info`, top after the struct (aligned); linked after `main_arena`; the caller's
`thread_arena`. `none` when the kernel refuses both heaps. -/
def newArena (w : World) (tid nb : Nat) : Option Nat × World :=
  let hdrs := C.heapInfoSize + C.stateSize + C.align
  let try1 := max (alignUp (nb + hdrs + C.topPad) C.page) heapMinSize
  let try2 := max (alignUp hdrs C.page) heapMinSize
  let attempt := heapAttempt C
  let (r, w) := match attempt w try1 with
    | (some r, w) => (some r, w)
    | (none, w) => attempt w try2
  match r with
  | none => (none, w)
  | some (h, sz) =>
    let a := h + C.heapInfoSize
    let p := a + C.stateSize
    let p := if (p + C.hdr) % C.align ≠ 0 then p + (C.align - (p + C.hdr) % C.align) else p
    let av : ArenaSt :=
      { tiles := { start := p, chunks := [], top := p, topSize := h + sz - p, noncontig := true,
                   systemMem := sz, maxSystemMem := sz }
        fast := { lists := fun _ => [], haveFast := false }
        bins := { lists := fun _ => [], binmap := fun _ => false }
        unsorted := { list := [], lastRem := 0 }
        attached := 1
        heaps := [(h, sz)]
        reserve := C.heapMaxSize - sz }
    let w := { w with
      arenas := fun x => if x = a then some av else w.arenas x
      shared := { w.shared with arenas := a :: w.shared.arenas, narenas := w.shared.narenas + 1 } }
    (some a, setArena w tid a)

/-- **`arena_get2 (size, avoid)`** (see the module note for the simplified reuse). -/
def arenaGet2 (w : World) (tid nb : Nat) : Res (Nat × World) :=
  match w.shared.freeList with
  | a :: rest =>
    .ok (a, setArena { w with shared := { w.shared with freeList := rest } } tid a)
  | [] =>
    if w.shared.narenas ≤ C.arenaTest then
      match newArena C w tid nb with
      | (some a, w) => .ok (a, w)
      | (none, w) => .ok (w.mainArena, setArena w tid w.mainArena)
    else .ok (w.mainArena, setArena w tid w.mainArena)

/-- **`arena_get (ar_ptr, size)`**: `thread_arena`, else `arena_get2`. -/
def arenaGet (w : World) (tid nb : Nat) : Res (Nat × World) :=
  match (w.threads tid).arena with
  | some a => .ok (a, w)
  | none => arenaGet2 C w tid nb

/-- **`arena_get_retry (ar_ptr, bytes)`**. -/
def arenaRetry (w : World) (tid a nb : Nat) : Res (Option Nat × World) :=
  if a ≠ w.mainArena then .ok (some w.mainArena, w)
  else (arenaGet2 C w tid nb).map fun (a, w) => (some a, w)

/-- `sizeof (tcache_perthread_struct)`. -/
def tcacheStructSize : Nat := C.tcacheBins * (C.tcacheCountWidth + 8)

/-- Label the chunk of payload `p` `internal` in arena `a` (or among the `mmap`ed chunks). -/
def markInternal (w : World) (a p : Nat) : World :=
  let c := p - C.hdr
  if w.shared.mm.chunks.any (·.addr = c) then
    { w with shared := { w.shared with mm := { w.shared.mm with
      chunks := w.shared.mm.chunks.map fun d => if d.addr = c then { d with use := .internal } else d } } }
  else
    { w with arenas := fun x =>
        if x = a then (w.arenas x).map fun av => { av with tiles := av.tiles.relabel c .internal }
        else w.arenas x }

/-- **`tcache_init`** for thread `tid` (`MAYBE_INIT_TCACHE`: only without a tcache). -/
def tcacheInit (w : World) (tid : Nat) : Res World := do
  let t := w.threads tid
  if t.tcache.isSome ∨ t.shuttingDown then return w
  let bytes := tcacheStructSize C
  let (a, w) ← arenaGet C w tid bytes
  let l ← Ops.localAt w tid a
  let (p, l) ← intMalloc C l bytes
  let w := w.put tid l
  let (a, p, w) ← if p ≠ 0 then pure (a, p, w) else do
    let (r, w) ← arenaRetry C w tid a bytes
    match r with
    | none => pure (a, 0, w)
    | some a' =>
      let l ← Ops.localAt w tid a'
      let (p, l) ← intMalloc C l bytes
      pure (a', p, w.put tid l)
  if p = 0 then return w
  let w := markInternal C w a p
  return { w with threads := fun x =>
    if x = tid then { w.threads x with tcache := some { addr := p, bins := fun _ => [] } } else w.threads x }

end Silmaril.Libc.Ptmalloc.Algo
