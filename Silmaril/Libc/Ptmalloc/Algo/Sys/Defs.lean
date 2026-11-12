module

public import Silmaril.Libc.Ptmalloc.Algo.Free.Defs
public import Silmaril.Libc.Ptmalloc.Algo.Mmapped.Defs

/-!
# ptmalloc algorithm: `sysmalloc`

glibc 2.39 `sysmalloc (nb, av)`, called when the top chunk cannot serve `nb`:

1. **`mmap` path**: `nb ≥ mp_.mmap_threshold` and `n_mmaps < n_mmaps_max`: `sysmalloc_mmap`.
2. **main arena** (`sysmallocMain`): `sbrk` of `ALIGN_UP (nb + top_pad + MINSIZE [− old top], page)`;
   on refusal the `mmap` fallback (`sysmalloc_mmap_fallback`, at least `MMAP_AS_MORECORE_SIZE`,
   making the arena non-contiguous); then either the contiguous extension of top, or a new top
   (front alignment and end correction by a second `sbrk` while contiguous) and the old top
   closed with two fence posts and freed (`_int_free (av, old_top, 1)`) when at least `MINSIZE`
   (W6/M3, `Seg.pad` for an old top of `MINSIZE + hdr` bytes).
3. **non-main arena** (`sysmallocHeap`): `grow_heap` of the current heap (`mprotect`), else
   `new_heap` (a `HEAP_MAX_SIZE`-aligned mapping) with the old top closed and freed, else the
   `mmap` path if not tried.
4. the final carve: `nb` bytes off top when it has `nb + MINSIZE`, else `ENOMEM` and 0.

The first `sbrk` of an arena (`start = 0`) never equals `old_end` (`initial_top` lies in the
arena struct, which the break area does not contain), so the model takes the new-top branch
there, as glibc does.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- `HEAP_MIN_SIZE` (32 KiB). -/
def heapMinSize : Nat := 0x8000

/-- The final carve (`sysmalloc`'s "finally, do the allocation"), after updating
`max_system_mem`. -/
def sysCarve (l : Local) (nb : Nat) : Nat × Local :=
  let ts := l.av.tiles
  let ts := { ts with maxSystemMem := max ts.systemMem ts.maxSystemMem }
  let l := withTiles l ts
  if ts.start ≠ 0 ∧ nb + C.minSize ≤ ts.topSize then
    (ts.top + C.hdr, withTiles l (ts.useTop nb .client))
  else (0, setErrno l 12)

/-- **Close the current segment** at a new top `top'` of `size'` bytes: glibc's old-top handling
for the main arena (`fences = 2`: old top shrunk by `2 * CHUNK_HDR_SZ`, two `CHUNK_HDR_SZ` fence
posts) and for a new non-main heap (`fences = 1`: old top shrunk by `MINSIZE`, the fence posts
`CHUNK_HDR_SZ` and 0). The old top, if at least `MINSIZE` afterwards, is a `client` chunk that
the caller frees; its address is returned. -/
def closeSegment (l : Local) (top' size' : Nat) (main : Bool) : Option Nat × Local :=
  let ts := l.av.tiles
  let oldSize := topSz ts
  let os := alignDown (oldSize - (if main then 2 * C.hdr else C.minSize)) C.align
  let keep := ts.start ≠ 0 ∧ oldSize ≠ 0
  let (seg, freed) : Option Seg × Option Nat :=
    if keep then
      if C.minSize ≤ os then
        (some { start := ts.start, chunks := ts.chunks ++ [(os, .client)] }, some ts.top)
      else if main then (some { start := ts.start, chunks := ts.chunks, pad := os }, none)
      else
        let stub := os + C.hdr
        if C.minSize ≤ stub then
          (some { start := ts.start, chunks := ts.chunks ++ [(stub, .internal)] }, none)
        else (some { start := ts.start, chunks := ts.chunks, pad := stub }, none)
    else if ts.start ≠ 0 then (some { start := ts.start, chunks := ts.chunks }, none)
    else (none, none)
  let ts' : TopSt :=
    { ts with
      start := top', chunks := [], top := top', topSize := size'
      old := ts.old ++ seg.toList }
  (freed, withTiles l ts')

/-- Free the closed old top, if any (`_int_free (av, old_top, 1)`). -/
def freeOldTop (l : Local) : Option Nat → Res Local
  | none => .ok l
  | some c => intFree C l c

/-- **`sysmalloc`, main arena** (after the `mmap` path). -/
def sysmallocMain (l : Local) (nb : Nat) : Res (Nat × Local) := do
  let ts := l.av.tiles
  let oldSize := topSz ts
  let oldEnd := ts.top + oldSize
  let contig := !ts.noncontig
  let size := alignUp (if contig then nb + C.topPad + C.minSize - oldSize else nb + C.topPad + C.minSize) C.page
  let (brk, k) := l.kernel.sbrk size
  let l := { l with kernel := k }
  -- the mmap fallback
  let (got, l) : Option (Nat × Option Nat × Nat) × Local :=
    match brk with
    | some b => (some (b, none, size), l)
    | none =>
      let fs := max (if contig then alignUp (size + oldSize) C.page else size) C.mmapAsMorecore
      if fs ≤ nb then (none, l) else
      match l.kernel.mmap C.page fs with
      | (none, k) => (none, { l with kernel := k })
      | (some m, k) =>
        (some (m, some (m + fs), fs),
          { l with kernel := k, av := { l.av with tiles := { l.av.tiles with noncontig := true } } })
  match got with
  | none => return sysCarve C l nb
  | some (b, snd, size) =>
    let mp := l.shared.mm.mp
    let l := { l with shared := { l.shared with mm := { l.shared.mm with
      mp := { mp with sbrkBase := if mp.sbrkBase = 0 then b else mp.sbrkBase } } } }
    let ts := l.av.tiles
    let ts := { ts with systemMem := ts.systemMem + size }
    let l := withTiles l ts
    if ts.start ≠ 0 ∧ b = oldEnd ∧ snd = none then
      -- contiguous extension of top
      return sysCarve C (withTiles l { ts with topSize := size + oldSize }) nb
    let contig := !ts.noncontig
    if contig ∧ oldSize ≠ 0 ∧ b < oldEnd then .error .breakAdjusted
    -- a new top: front alignment and end correction while contiguous
    let (aligned, snd', corr, l) : Nat × Nat × Nat × Local :=
      if contig then
        let gap := if oldSize ≠ 0 then b - oldEnd else 0
        let l := withTiles l { l.av.tiles with systemMem := l.av.tiles.systemMem + gap }
        let front := (b + C.hdr) % C.align
        let c0 := if front > 0 then C.align - front else 0
        let c1 := c0 + oldSize
        let e := b + size + c1
        let c2 := c1 + (alignUp e C.page - e)
        match l.kernel.sbrk c2 with
        | (some s, k) => (b + c0, s, c2, { l with kernel := k })
        | (none, k) => (b + c0, k.brk, 0, { l with kernel := k })
      else (b, snd.getD l.kernel.brk, 0, l)
    let newSize := snd' - aligned + corr
    let l := withTiles l { l.av.tiles with systemMem := l.av.tiles.systemMem + corr }
    let (freed, l) := closeSegment C l aligned newSize true
    let l ← freeOldTop C l freed
    return sysCarve C l nb

/-- The `mmap` path as `sysmalloc`'s last resort for a non-main arena (when not tried yet). -/
def heapLastResort (l : Local) (nb : Nat) (tried : Bool) : Nat × Local :=
  if tried then sysCarve C l nb else
  match sysmallocMmap C l nb with
  | (some p, l) => (p, l)
  | (none, l) => sysCarve C l nb

/-- `new_heap` for `nb` and the old top closed into a segment (non-main arena). -/
def sysNewHeap (l : Local) (nb : Nat) (tried : Bool) : Res (Nat × Local) := do
  let want := alignUp (nb + C.minSize + C.heapInfoSize + C.topPad) C.page
  let need := alignUp (nb + C.minSize + C.heapInfoSize) C.page
  let hsize := if want ≤ C.heapMaxSize then max want heapMinSize else need
  if C.heapMaxSize < hsize then return heapLastResort C l nb tried
  match l.kernel.mmap C.heapMaxSize C.heapMaxSize with
  | (none, k) => return heapLastResort C { l with kernel := k } nb tried
  | (some h', k) =>
    let av := { l.av with heaps := (h', hsize) :: l.av.heaps, reserve := C.heapMaxSize - hsize }
    let l := { l with kernel := k, av := av }
    let l := withTiles l { l.av.tiles with systemMem := l.av.tiles.systemMem + hsize }
    let (freed, l) := closeSegment C l (h' + C.heapInfoSize) (hsize - C.heapInfoSize) false
    let l ← freeOldTop C l freed
    return sysCarve C l nb

/-- **`sysmalloc`, non-main arena** (after the `mmap` path; `tried` = it was tried):
`grow_heap`, else `new_heap`, else the `mmap` path. -/
def sysmallocHeap (l : Local) (nb : Nat) (tried : Bool) : Res (Nat × Local) := do
  let ts := l.av.tiles
  let oldSize := topSz ts
  let some (h, hs) := l.av.heaps.head? | .error .internal
  let diff := alignUp (C.minSize + nb - oldSize) C.page
  if 0 < C.minSize + nb - oldSize ∧ hs + diff ≤ C.heapMaxSize then
    match l.kernel.mprotect with
    | (true, k) =>
      let av := { l.av with heaps := (h, hs + diff) :: l.av.heaps.tail, reserve := l.av.reserve - diff }
      let l := { l with kernel := k, av := av }
      return sysCarve C (withTiles l
        { ts with systemMem := ts.systemMem + diff, topSize := h + hs + diff - ts.top }) nb
    | (false, k) => sysNewHeap C { l with kernel := k } nb tried
  else sysNewHeap C l nb tried

/-- **`sysmalloc (nb, av)`**. -/
def sysmalloc (l : Local) (nb : Nat) : Res (Nat × Local) := do
  let mp := l.shared.mm.mp
  let (tried, l) ←
    if mp.mmapThreshold ≤ nb ∧ mp.nMmaps < C.mmapMax then
      match sysmallocMmap C l nb with
      | (some p, l) => return (p, l)
      | (none, l) => pure (true, l)
    else pure (false, l)
  if l.isMain then sysmallocMain C l nb else sysmallocHeap C l nb tried

end Silmaril.Libc.Ptmalloc.Algo
