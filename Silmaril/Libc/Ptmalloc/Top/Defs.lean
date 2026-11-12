module

public import Silmaril.Libc.Ptmalloc.Chunk.Defs

/-!
# ptmalloc component: the tiling and the top chunk (per arena)

State `TopSt`: the arena's heap as a tiling (the current segment's chunks, which end at the top
chunk; closed segments with their fence posts), the top chunk, `system_mem`, `max_system_mem`
and the contiguity flag. Invariant `TopWF` (sizes, alignment, adjacency, coalescing incl. closed
segments (W15c), `system_mem` (W16b), top at least `MINSIZE`, distinct chunk addresses).

Operations, each on **runs** (`List (Nat × Use)` laid out from a start address, so adjacency is
by construction):

| operation | glibc | run function |
|---|---|---|
| `relabel a u` | every use change (bin in/out, lent out) | `relabelRun` |
| `split a s₁ u₁ u₂` | carving `nb` bytes off a free chunk (remainders) | `splitRun` |
| `fuse a u` | merging a chunk with the next one (`_int_free`'s and `malloc_consolidate`'s coalescing) | `fuseRun` |
| `useTop nb u` | `_int_malloc`'s `use_top`, `sysmalloc`'s final carve | — |
| `mergeTop` | merging the current segment's last chunk into top | — |
| `locate a` | `prev_inuse`/`chunk_at_offset`: the neighbours of a chunk | `locRun` |

`sysmalloc`/`systrim` are bodies over this component and the kernel (`Silmaril.Libc.Ptmalloc.Algo`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-! ## Runs -/

/-- Split the entry at address `a` (run from `s`) into `s₁` bytes of use `u₁` and the rest of
use `u₂`. -/
def splitRun (a s₁ : Nat) (u₁ u₂ : Use) : Nat → List (Nat × Use) → List (Nat × Use)
  | _, [] => []
  | s, (sz, v) :: cs =>
    if s = a then (s₁, u₁) :: (sz - s₁, u₂) :: cs else (sz, v) :: splitRun a s₁ u₁ u₂ (s + sz) cs

/-- Fuse the entry at address `a` (run from `s`) with the next entry, as one entry of use `u`
(no change when `a` is the last entry). -/
def fuseRun (a : Nat) (u : Use) : Nat → List (Nat × Use) → List (Nat × Use)
  | _, [] => []
  | s, (sz, v) :: cs =>
    if s = a then
      match cs with
      | (sz', _) :: rest => (sz + sz', u) :: rest
      | [] => [(sz, v)]
    else (sz, v) :: fuseRun a u (s + sz) cs

/-- The entry at `a` of a run from `s`, with the entry before it (if any) and after it (if any). -/
def locRun (a : Nat) : Nat → Option Chunk → List (Nat × Use) →
    Option (Option Chunk × Chunk × Option Chunk)
  | _, _, [] => none
  | s, prev, (sz, v) :: cs =>
    if s = a then some (prev, ⟨s, sz, v⟩, cs.head?.map fun e => ⟨s + sz, e.1, e.2⟩)
    else locRun a (s + sz) (some ⟨s, sz, v⟩) cs

/-- No two adjacent entries of a run are both in regular bins (boolean form). -/
def coalescedB : List (Nat × Use) → Bool
  | a :: b :: cs => !(a.2.tagFree && b.2.tagFree) && coalescedB (b :: cs)
  | _ => true

/-- No two adjacent chunks of a run are both in regular bins. -/
def Coalesced (cs : List (Nat × Use)) : Prop := coalescedB cs = true

instance (cs : List (Nat × Use)) : Decidable (Coalesced cs) := by
  unfold Coalesced; exact inferInstance

/-! ## The component -/

/-- **The tiling and the top chunk.** -/
structure TopSt where
  /-- The current segment's start (0: no heap yet) and its chunks, ending at the top chunk. -/
  start : Nat
  chunks : List (Nat × Use)
  /-- Closed segments. -/
  old : List Seg := []
  top : Nat
  topSize : Nat
  noncontig : Bool
  systemMem : Nat
  maxSystemMem : Nat

/-- What follows a chunk: another chunk of its run, the top chunk (end of the current segment),
or a fence post (end of a closed segment). -/
inductive Nbr where
  | chunk (c : Chunk)
  | top
  | fence
  deriving DecidableEq, Repr

/-- A chunk located in the tiling: the chunk before it in its run, the chunk, what follows it,
and whether it lies in the current segment. -/
structure Loc where
  prev : Option Chunk
  self : Chunk
  next : Nbr
  current : Bool
  deriving DecidableEq, Repr

namespace TopSt

variable (ts : TopSt)

/-- All chunks of the tiling (closed segments first). -/
def heapChunks : List Chunk :=
  (ts.old.flatMap fun g => layout g.start g.chunks) ++ layout ts.start ts.chunks

/-- The byte ranges the tiling owns: its chunks and, once there is a heap, the top chunk. -/
def spans : List (Nat × Nat) :=
  ts.heapChunks.map (fun c => (c.addr, c.size)) ++ (if ts.start = 0 then [] else [(ts.top, ts.topSize)])

/-- The size of the chunk at `a` (0 if none). -/
def sizeAt (a : Nat) : Nat := ((ts.heapChunks.find? (·.addr = a)).map (·.size)).getD 0

/-- The chunk at `a`, if any. -/
def find? (a : Nat) : Option Chunk := ts.heapChunks.find? (·.addr = a)

/-- Relabel the chunk at `a` (in whichever segment). -/
def relabel (a : Nat) (u : Use) : TopSt :=
  { ts with
    chunks := relabelRun a u ts.start ts.chunks
    old := ts.old.map fun g => { g with chunks := relabelRun a u g.start g.chunks } }

/-- Split the chunk at `a` (in whichever segment) into `s₁` bytes of use `u₁` and the rest of use
`u₂`. -/
def split (a s₁ : Nat) (u₁ u₂ : Use) : TopSt :=
  { ts with
    chunks := splitRun a s₁ u₁ u₂ ts.start ts.chunks
    old := ts.old.map fun g => { g with chunks := splitRun a s₁ u₁ u₂ g.start g.chunks } }

/-- Fuse the chunk at `a` with the chunk after it (in whichever segment), as one chunk of use `u`. -/
def fuse (a : Nat) (u : Use) : TopSt :=
  { ts with
    chunks := fuseRun a u ts.start ts.chunks
    old := ts.old.map fun g => { g with chunks := fuseRun a u g.start g.chunks } }

/-- **`use_top`**: carve `nb` bytes from the top chunk as a new last chunk of use `u`. -/
def useTop (nb : Nat) (u : Use) : TopSt :=
  { ts with chunks := ts.chunks ++ [(nb, u)], top := ts.top + nb, topSize := ts.topSize - nb }

/-- Merge the last chunk of the current segment back into top. -/
def mergeTop : TopSt :=
  match ts.chunks.getLast? with
  | none => ts
  | some (s, _) => { ts with chunks := ts.chunks.dropLast, top := ts.top - s, topSize := ts.topSize + s }

/-- Locate the chunk at `a`: the current segment first, then the closed segments. -/
def locate (a : Nat) : Option Loc :=
  match locRun a ts.start none ts.chunks with
  | some (p, c, n) => some ⟨p, c, (n.map Nbr.chunk).getD .top, true⟩
  | none =>
    (ts.old.findSome? fun g => locRun a g.start none g.chunks).map fun (p, c, n) =>
      ⟨p, c, (n.map Nbr.chunk).getD .fence, false⟩

end TopSt

/-- **The tiling's invariant.** -/
structure TopWF (C : Config) (ts : TopSt) : Prop where
  sizes : ∀ c ∈ ts.heapChunks, c.size % C.align = 0 ∧ C.minSize ≤ c.size
  aligned : ∀ c ∈ ts.heapChunks, c.addr % C.align = 0
  nonNull : ∀ c ∈ ts.heapChunks, c.addr ≠ 0
  topAt : ts.start ≠ 0 → ts.top = ts.start + (ts.chunks.map (·.1)).sum
  topAligned : ts.top % C.align = 0 ∧ ts.topSize % C.align = 0
  topMin : ts.start ≠ 0 → C.minSize ≤ ts.topSize
  coalesced : Coalesced ts.chunks
  lastUsed : ∀ c ∈ ts.chunks.getLast?, c.2.tagFree = false
  coalescedOld : ∀ g ∈ ts.old, Coalesced g.chunks
  sysMem : (ts.heapChunks.map (·.size)).sum + ts.topSize ≤ ts.systemMem
  sysMemBound : ts.systemMem < 2 ^ 64
  noHeap : ts.start = 0 → ts.chunks = [] ∧ ts.old = []
  /-- Chunk addresses are distinct (closed segments are apart from each other and from the
  current one; within a run, addresses increase). Needed so that a relabel, split or fuse at an
  address acts on one chunk. -/
  nodup : (ts.heapChunks.map (·.addr)).Nodup
  /-- Every chunk and the top chunk lie below `2 ^ 64` (the kernel maps nothing above its user
  address space; `last_remainder` and returned payloads are words). -/
  bound : ∀ c ∈ ts.heapChunks, c.addr + c.size < 2 ^ 64
  topBound : ts.start ≠ 0 → ts.top + ts.topSize < 2 ^ 64

end Silmaril.Libc.Ptmalloc
