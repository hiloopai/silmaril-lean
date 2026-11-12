module

public import Silmaril.Libc.Ptmalloc.Heap.Defs

/-!
# ptmalloc: the composition theorems

A path proof that changes one component re-establishes `ArenaWF` from that component's new
invariant and "the other components' views did not change". `withFast` (fastbin paths),
`withBins`, `withUnsorted`, `withTiles` are proved here; the view lemmas they need for a
relabelling (`Task.algo.viewRelabel`) are the `algo` builder's.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

namespace ArenaWF

variable {C : Config} {av : ArenaSt}

/-- **Fastbin paths**: new fastbins and tiling; the other views unchanged. -/
theorem withFast (h : ArenaWF C av) (ts : TopSt) (fs : FastSt) (ht : TopWF C ts)
    (hf : FastWF C fs (Chunk.view Use.isFast ts.heapChunks))
    (hs : Chunk.view Use.isSorted ts.heapChunks = av.sortedView) (hsz : ts.sizeAt = av.tiles.sizeAt)
    (hu : Chunk.view Use.isUnsorted ts.heapChunks = av.unsortedView)
    (hi : ∀ c ∈ ts.heapChunks, c.use = .internal → C.minSize ≤ c.size) :
    ArenaWF C { av with tiles := ts, fast := fs } where
  tiles := ht
  fast := hf
  bins := by
    show BinsWF C av.bins (Chunk.view Use.isSorted ts.heapChunks) ts.sizeAt
    rw [hs, hsz]; exact h.bins
  unsorted := by
    show UnsortedWF C av.unsorted (Chunk.view Use.isUnsorted ts.heapChunks)
    rw [hu]; exact h.unsorted
  internal := hi

/-- **Bin paths**: new bins and tiling; the other views unchanged. -/
theorem withBins (h : ArenaWF C av) (ts : TopSt) (bs : BinsSt) (ht : TopWF C ts)
    (hb : BinsWF C bs (Chunk.view Use.isSorted ts.heapChunks) ts.sizeAt)
    (hf : Chunk.view Use.isFast ts.heapChunks = av.fastView)
    (hu : Chunk.view Use.isUnsorted ts.heapChunks = av.unsortedView)
    (hi : ∀ c ∈ ts.heapChunks, c.use = .internal → C.minSize ≤ c.size) :
    ArenaWF C { av with tiles := ts, bins := bs } where
  tiles := ht
  fast := by
    show FastWF C av.fast (Chunk.view Use.isFast ts.heapChunks)
    rw [hf]; exact h.fast
  bins := hb
  unsorted := by
    show UnsortedWF C av.unsorted (Chunk.view Use.isUnsorted ts.heapChunks)
    rw [hu]; exact h.unsorted
  internal := hi

/-- **Unsorted paths**: new unsorted bin and tiling; the other views unchanged. -/
theorem withUnsorted (h : ArenaWF C av) (ts : TopSt) (us : UnsortedSt) (ht : TopWF C ts)
    (hu : UnsortedWF C us (Chunk.view Use.isUnsorted ts.heapChunks))
    (hf : Chunk.view Use.isFast ts.heapChunks = av.fastView)
    (hs : Chunk.view Use.isSorted ts.heapChunks = av.sortedView) (hsz : ts.sizeAt = av.tiles.sizeAt)
    (hi : ∀ c ∈ ts.heapChunks, c.use = .internal → C.minSize ≤ c.size) :
    ArenaWF C { av with tiles := ts, unsorted := us } where
  tiles := ht
  fast := by
    show FastWF C av.fast (Chunk.view Use.isFast ts.heapChunks)
    rw [hf]; exact h.fast
  bins := by
    show BinsWF C av.bins (Chunk.view Use.isSorted ts.heapChunks) ts.sizeAt
    rw [hs, hsz]; exact h.bins
  unsorted := hu
  internal := hi

/-- **Top paths** (`use_top`, `sysmalloc`, `systrim`): new tiling; no list's view changes. -/
theorem withTiles (h : ArenaWF C av) (ts : TopSt) (ht : TopWF C ts)
    (hf : Chunk.view Use.isFast ts.heapChunks = av.fastView)
    (hs : Chunk.view Use.isSorted ts.heapChunks = av.sortedView) (hsz : ts.sizeAt = av.tiles.sizeAt)
    (hu : Chunk.view Use.isUnsorted ts.heapChunks = av.unsortedView)
    (hi : ∀ c ∈ ts.heapChunks, c.use = .internal → C.minSize ≤ c.size) :
    ArenaWF C { av with tiles := ts } :=
  (h.withFast ts av.fast ht (by rw [hf]; exact h.fast) hs hsz hu hi)

end ArenaWF

/-- **`Task.algo.viewRelabel`**: relabelling a chunk between two uses a component does not see
leaves that component's view (e.g. a fastbin pop, `fast i → client`, leaves the sorted and
unsorted views). -/
def Task.algo.viewRelabel : Prop :=
  ∀ (ts : TopSt) (a : Nat) (u : Use) (p : Use → Bool),
    (∀ c ∈ ts.heapChunks, c.addr = a → p c.use = false) → p u = false →
    Chunk.view p (ts.relabel a u).heapChunks = Chunk.view p ts.heapChunks

end Silmaril.Libc.Ptmalloc
