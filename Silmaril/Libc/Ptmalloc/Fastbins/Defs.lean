module

public import Silmaril.Libc.Ptmalloc.Chunk.Defs

/-!
# ptmalloc component: the fastbins (per arena)

State `FastSt` (the `C.nFast` LIFO lists and `have_fastchunks`), invariant `FastWF` against the
arena's **fast view** (`Chunk.view Use.isFast`), operations `push` and `pop`. The relabelling
of the chunk in the tiling is the arena's (`Silmaril.Libc.Ptmalloc.Heap`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **The fastbins.** -/
structure FastSt where
  lists : Nat → List Nat
  haveFast : Bool

namespace FastSt

variable (fs : FastSt)

/-- Push chunk `a` on fastbin `i`; `have_fastchunks` set. -/
def push (a i : Nat) : FastSt :=
  { lists := fun j => if j = i then a :: fs.lists j else fs.lists j, haveFast := true }

/-- Pop the head of fastbin `i`. -/
def pop (i : Nat) : Option (Nat × FastSt) :=
  match fs.lists i with
  | [] => none
  | a :: rest => some (a, { fs with lists := fun j => if j = i then rest else fs.lists j })

/-- Empty every fastbin (`malloc_consolidate`'s outer loop, as a whole). -/
def clear : FastSt := { lists := fun _ => [], haveFast := false }

end FastSt

/-- **The fastbins' invariant** against the fast view `cs` (chunks whose use is `fast _`). -/
structure FastWF (C : Config) (fs : FastSt) (cs : List Chunk) : Prop where
  exact : ∀ i, ListExact (fs.lists i) cs (.fast i)
  nodup : ∀ i, (fs.lists i).Nodup
  size : ∀ c ∈ cs, ∀ i, c.use = .fast i → C.fidx c.size = i ∧ c.size ≤ C.maxFast ∧ i < C.nFast
  /-- `have_fastchunks` is set when a fastbin is non-empty (it may stay set when empty). -/
  flag : (∃ i, fs.lists i ≠ []) → fs.haveFast = true

end Silmaril.Libc.Ptmalloc
