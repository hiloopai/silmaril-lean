module

public import Silmaril.Libc.Ptmalloc.Algo.Sys.Defs

/-!
# ptmalloc algorithm: `_int_malloc`

glibc 2.39 `_int_malloc (av, bytes)`, path by path, each a function of its own so that a path
proof mentions only the components it touches:

| path | function | components |
|---|---|---|
| fastbin hit, tcache refill from the same fastbin | `mallocFast`, `fastRefill` | Fastbins, Top (relabel), Tcache |
| small-bin hit (`last (bin)`), tcache refill | `mallocSmall`, `smallRefill` | Bins, Top (relabel), Tcache |
| large request: `malloc_consolidate` first if `have_fastchunks` | `intMalloc` | Fastbins, Bins, Unsorted, Top |
| unsorted scan (`last_remainder` split, exact fit, tcache stash, sorting into bins, `MAX_ITERS`, `tcache_unsorted_limit`) | `unsortedScan` | Unsorted, Bins, Top, Tcache |
| large-bin best fit (smallest fitting size; the group's second chunk when there is one) | `largeFit`, `takeFit` | Bins, Unsorted (remainder), Top |
| bin-map scan (first marked non-empty bin above the request's; empty marked bins unmarked) | `binmapScan`, `takeFit` | Bins, Unsorted (remainder, `last_remainder`), Top |
| `use_top`; else `malloc_consolidate` and again; else `sysmalloc` | `mallocLoop` | Top, Fastbins, … |

The outer `for (;;)` runs at most twice: the second time `have_fastchunks` is clear (nothing in
the loop puts a chunk in a fastbin), so `use_top` ends in `sysmalloc`; the model's fuel is 3.
The unsorted scan's fuel is the unsorted list's length (each step removes the victim or
returns).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- The tcache refill from fastbin `i` for tcache bin `t` (`while (tcache->counts[tc_idx] <
mp_.tcache_count && (tc_victim = *fb) != NULL)`). -/
def fastRefill (i t : Nat) : Nat → Local → Res Local
  | 0, l => .ok l
  | fuel + 1, l =>
    if tcCount l t < C.tcacheCount then
      match l.av.fast.lists i with
      | [] => .ok l
      | a :: _ =>
        if a % C.align ≠ 0 then .error .unalignedFastbin else
        match l.fastPop i with
        | none => .ok l
        | some (a, l) => fastRefill i t fuel (tcPut l (a, l.av.tiles.sizeAt a) t)
    else .ok l

/-- **The fastbin path**: the head of fastbin `fidx nb`, lent out; the refill. `none`: empty bin. -/
def mallocFast (l : Local) (nb : Nat) : Res (Option (Nat × Local)) :=
  let i := C.fidx nb
  match l.av.fast.lists i with
  | [] => .ok none
  | a :: _ =>
    if a % C.align ≠ 0 then .error .unalignedFastbin else
    match l.fastPop i with
    | none => .ok none
    | some (a, l) =>
      if C.fidx (l.av.tiles.sizeAt a) ≠ i then .error .mallocMemoryCorruption else
      let t := C.tidx nb
      if tcOn C l t then
        (fastRefill C i t C.tcacheCount l).map fun l => some (a + C.hdr, l)
      else .ok (some (a + C.hdr, l))

/-- The tcache refill from small bin `i` (`last (bin)` first). -/
def smallRefill (i t : Nat) : Nat → Local → Local
  | 0, l => l
  | fuel + 1, l =>
    if tcCount l t < C.tcacheCount then
      match l.av.bins.last? i with
      | none => l
      | some v =>
        let l := l.binRemove v i .client
        smallRefill i t fuel (tcPut l (v, l.av.tiles.sizeAt v) t)
    else l

/-- **The small-bin path**: `last (bin)` of `smallbin_index (nb)`, lent out; the refill. -/
def mallocSmall (l : Local) (nb : Nat) : Option (Nat × Local) :=
  let i := C.binIndex nb
  match l.av.bins.last? i with
  | none => none
  | some v =>
    let l := l.binRemove v i .client
    let t := C.tidx nb
    some (v + C.hdr, if tcOn C l t then smallRefill C i t C.tcacheCount l else l)

/-- The outcome of the unsorted scan. -/
inductive ScanRes where
  /-- Return this payload. -/
  | done (p : Nat)
  /-- `return tcache_get (tc_idx)` (`return_cached`). -/
  | cached
  /-- Go on to the large-bin and bin-map paths. -/
  | cont

/-- **The unsorted scan** (`while ((victim = unsorted_chunks (av)->bk) != unsorted_chunks (av))`),
with `iters`, `return_cached` and `tcache_unsorted_count`. -/
def unsortedScan (nb : Nat) (tcNb : Bool) : Nat → Nat → Bool → Nat → Local → Res (ScanRes × Local)
  | 0, _, rc, _, l => .ok (if rc then .cached else .cont, l)
  | fuel + 1, iters, rc, cnt, l =>
    match l.av.unsorted.list.getLast? with
    | none => .ok (if rc then .cached else .cont, l)
    | some v =>
      let size := l.av.tiles.sizeAt v
      if size ≤ C.hdr ∨ l.av.tiles.systemMem < size then .error .mallocMemoryCorruption else
      -- the last remainder
      if C.inSmallRange nb ∧ l.av.unsorted.list.length = 1 ∧ v = l.av.unsorted.lastRem ∧
          nb + C.minSize < size then
        let r := v + nb
        .ok (.done (v + C.hdr),
          { l with av := { l.av with
              tiles := l.av.tiles.split v nb .client (.bin 1)
              unsorted := { list := [r], lastRem := r } } })
      else
      match unsortedTake l with
      | none => .error .internal
      | some (v, l) =>
        if size = nb then
          if tcNb ∧ tcCount l (C.tidx nb) < C.tcacheCount then
            unsortedScan nb tcNb fuel iters true cnt (tcPut (l.relabel v .client) (v, size) (C.tidx nb))
          else .ok (.done (v + C.hdr), l.relabel v .client)
        else
        let l := if C.inSmallRange size then l.binPushFront v (C.binIndex size)
          else largeInsert l v (C.binIndex size)
        let cnt := cnt + 1
        if rc ∧ 0 < C.tcacheUnsortedLimit ∧ C.tcacheUnsortedLimit < cnt then .ok (.cached, l) else
        if C.unsortedMaxIters ≤ iters + 1 then .ok (if rc then .cached else .cont, l) else
        unsortedScan nb tcNb fuel (iters + 1) rc cnt l

/-- **The large-bin best fit** in bin `binIndex nb`: the first chunk of the smallest size
`≥ nb` (walking `bk_nextsize` from the smallest group), or that group's second chunk when it has
one (glibc avoids relinking `nextsize`). -/
def largeFit (l : Local) (nb : Nat) : Option Nat :=
  let lst := l.av.bins.lists (C.binIndex nb)
  let sz := l.av.tiles.sizeAt
  match lst with
  | [] => none
  | h :: _ =>
    if sz h < nb then none else
    let s := ((lst.filter fun b => nb ≤ sz b).map sz).foldl min (sz h)
    let j := lst.findIdx fun b => sz b = s
    match lst[j + 1]? with
    | some b' => if sz b' = s then some b' else lst[j]?
    | none => lst[j]?

/-- **Take a fitting chunk** `v` from bin `i` for `nb` bytes: unlink it; if the remainder is at
least `MINSIZE`, split it off to the unsorted head (and make it `last_remainder` when `lastRem`),
else lend out the whole chunk. -/
def takeFit (l : Local) (v i nb : Nat) (lastRem : Bool) : Nat × Local :=
  let size := l.av.tiles.sizeAt v
  let l := l.binRemove v i .internal
  if size - nb < C.minSize then (v + C.hdr, l.relabel v .client)
  else
    let l := splitToUnsorted l v nb .client
    (v + C.hdr, if lastRem then { l with av := { l.av with unsorted := l.av.unsorted.setLastRem (v + nb) } } else l)

/-- **The bin-map scan** from bin `j` (`fuel` bins): the first marked non-empty bin; marked empty
bins on the way are unmarked. -/
def binmapScan : Nat → Nat → Local → Option (Nat × Nat) × Local
  | 0, _, l => (none, l)
  | fuel + 1, j, l =>
    if C.nBins ≤ j then (none, l) else
    if l.av.bins.binmap j then
      match l.av.bins.last? j with
      | some v => (some (v, j), l)
      | none => binmapScan fuel (j + 1) { l with av := { l.av with bins := l.av.bins.unmark j } }
    else binmapScan fuel (j + 1) l

/-- **The main loop** of `_int_malloc` (after the fastbin and small-bin paths). -/
def mallocLoop (nb : Nat) : Nat → Local → Res (Nat × Local)
  | 0, _ => .error .internal
  | fuel + 1, l => do
    let t := C.tidx nb
    let tcNb := tcOn C l t
    let (r, l) ← unsortedScan C nb tcNb (l.av.unsorted.list.length) 0 false 0 l
    match r with
    | .done p => return (p, l)
    | .cached =>
      match l.tcacheGet C t with
      | some (p, l) => return (p, l)
      | none => .error .internal
    | .cont =>
    -- the large-bin best fit
    if !C.inSmallRange nb then
      match largeFit C l nb with
      | some v => return takeFit C l v (C.binIndex nb) nb false
      | none => pure ()
    -- the bin-map scan
    match binmapScan C C.nBins (C.binIndex nb + 1) l with
    | (some (v, j), l) => return takeFit C l v j nb (C.inSmallRange nb)
    | (none, l) =>
    -- use_top
    let ts := l.av.tiles
    if ts.start ≠ 0 ∧ ts.systemMem < ts.topSize then .error .corruptedTopSize
    if ts.start ≠ 0 ∧ nb + C.minSize ≤ ts.topSize then
      return (ts.top + C.hdr, withTiles l (ts.useTop nb .client))
    if l.av.fast.haveFast then
      let l ← consolidate C l
      mallocLoop nb fuel l
    else sysmalloc C l nb

/-- **`_int_malloc (av, bytes)`**: the payload (0: refused, `errno` set). -/
def intMalloc (l : Local) (n : Nat) : Res (Nat × Local) := do
  let some nb := C.checkedRequest2size n | return (0, setErrno l 12)
  if nb ≤ C.maxFast then
    if let some r ← mallocFast C l nb then return r
  if C.inSmallRange nb then
    if let some r := mallocSmall C l nb then return r
    mallocLoop C nb 3 l
  else
    let l ← if l.av.fast.haveFast then consolidate C l else pure l
    mallocLoop C nb 3 l

end Silmaril.Libc.Ptmalloc.Algo
