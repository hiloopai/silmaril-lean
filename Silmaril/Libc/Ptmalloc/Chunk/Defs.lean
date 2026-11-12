module

public import Silmaril.Libc.Ptmalloc.Config.Defs

/-!
# ptmalloc: chunks, their uses, runs and segments

Shared vocabulary of the component sub-models (`Tcache`, `Fastbins`, `Bins`, `Unsorted`, `Top`,
`Mmap`). Each component sees the arena's chunk tiling only through its **view**
(`Chunk.view p cs`: the chunks whose use satisfies `p`), so a change of a chunk's use that the
component does not care about leaves its view, and so its invariant, unchanged.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **The use of a chunk, from its arena's point of view.** A tcache chunk is `client`: lent
out of the arena (no arena lock protects it) and parked in a thread's tcache. -/
inductive Use where
  /-- Lent out of the arena: allocated to the program, or in some thread's tcache. -/
  | client
  /-- Allocated to the allocator itself (a `tcache_perthread_struct`). -/
  | internal
  /-- In fastbin `i`. -/
  | fast (i : Nat)
  /-- In regular bin `i` (1 unsorted, 2–63 small, 64–126 large). -/
  | bin (i : Nat)
  deriving DecidableEq, Repr

/-- Free in the sense of the boundary tags: in a regular bin. -/
def Use.tagFree : Use → Bool
  | .bin _ => true
  | _ => false

/-- In a fastbin. -/
def Use.isFast : Use → Bool
  | .fast _ => true
  | _ => false

/-- In a small or large bin (not the unsorted bin). -/
def Use.isSorted : Use → Bool
  | .bin i => decide (2 ≤ i)
  | _ => false

/-- In the unsorted bin. -/
def Use.isUnsorted : Use → Bool
  | .bin 1 => true
  | _ => false

/-- A chunk: the address of its `prev_size` field, its size and its use. -/
structure Chunk where
  addr : Nat
  size : Nat
  use : Use
  deriving DecidableEq, Repr

/-- A component's view of a tiling: the chunks whose use satisfies `p`. -/
def Chunk.view (p : Use → Bool) (cs : List Chunk) : List Chunk := cs.filter (p ·.use)

/-- The chunks of a run of adjacent chunks from `a`. -/
def layout : Nat → List (Nat × Use) → List Chunk
  | _, [] => []
  | a, (s, u) :: cs => ⟨a, s, u⟩ :: layout (a + s) cs

/-- Relabel the chunk at `a` in a run of adjacent chunks from `start`. -/
def relabelRun (a : Nat) (u : Use) : Nat → List (Nat × Use) → List (Nat × Use)
  | _, [] => []
  | s, (sz, v) :: cs => (sz, if s = a then u else v) :: relabelRun a u (s + sz) cs

/-- A closed heap segment: chunks from `start`, then `pad` bytes (0, or `hdr` when `sysmalloc`
closed it on an old top of `MINSIZE + hdr` bytes: glibc writes an in-use `hdr`-byte stub there),
then two fence posts in its last `2 * hdr` bytes (W17/M3: it ends at
`start + Σ sizes + pad + 2 * hdr`). -/
structure Seg where
  start : Nat
  chunks : List (Nat × Use)
  pad : Nat := 0
  deriving DecidableEq, Repr

/-- The segment's end (the first fence post's address). -/
def Seg.endAddr (g : Seg) : Nat := g.start + (g.chunks.map (·.1)).sum + g.pad

/-- The segment's last chunk is in a regular bin (W6: the first fence post's `PREV_INUSE` is
clear). -/
def Seg.lastFree (g : Seg) : Bool := g.chunks.getLast?.any (·.2.tagFree)

/-- The usable size of a chunk (`chunksize - SIZE_SZ`, minus another word when `mmap`ed). -/
def usable (C : Config) (c : Chunk) (mm : Bool) : Nat :=
  if mm then c.size - 2 * C.sizeSz else c.size - C.sizeSz

/-- **Byte ranges `(start, length)` pairwise apart and non-empty.** -/
def Apart (rs : List (Nat × Nat)) : Prop :=
  rs.Pairwise (fun r r' => r.1 + r.2 ≤ r'.1 ∨ r'.1 + r'.2 ≤ r.1) ∧ ∀ r ∈ rs, 0 < r.2

/-- The range `r` is apart from every range of `rs`. -/
def Away (rs : List (Nat × Nat)) (r : Nat × Nat) : Prop :=
  ∀ s ∈ rs, r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1

/-- Every address of `l` is the address of a chunk of `cs` with use `u`, and conversely. -/
def ListExact (l : List Nat) (cs : List Chunk) (u : Use) : Prop :=
  ∀ a, a ∈ l ↔ ∃ c ∈ cs, c.addr = a ∧ c.use = u

end Silmaril.Libc.Ptmalloc
