module

public import Silmaril.Libc.Ptmalloc.Algo.Defs

/-!
# ptmalloc algorithm: the steps the bodies are built from

Every body of `Silmaril.Libc.Ptmalloc.Algo` (`_int_malloc`, `_int_free`, `malloc_consolidate`,
`sysmalloc`, …) is a sequence of the **steps** below and the leaf operations of
`Silmaril.Libc.Ptmalloc.Algo.Defs`. Each step changes one or two components and keeps `LocalWF`
under a local precondition (`Silmaril.Libc.Ptmalloc.Algo.Step.Thms`), so a body's
well-formedness proof is a chain of step lemmas, and the x86 block that implements a step is
matched against it once.

**The `internal` label while a body holds a chunk.** A chunk a body has taken out of a list (or
is about to give back) is labelled `internal`: it is neither lent out (`client`, counted in
`ArenaSt.out`) nor in a list, so every intermediate state is well formed and the live set
changes exactly once per call (at the step that labels the result `client`, or the freed chunk
`internal`). glibc's own `internal` chunk (the `tcache_perthread_struct`) has the same status.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

/-- `ALIGN_UP (x, a)`. -/
def alignUp (x a : Nat) : Nat := (x + a - 1) / a * a

/-- `ALIGN_DOWN (x, a)`. -/
def alignDown (x a : Nat) : Nat := x / a * a

variable (C : Config)

/-- The top chunk's size as glibc reads it (`initial_top` has size 0 before the first `sysmalloc`). -/
def topSz (ts : TopSt) : Nat := if ts.start = 0 then 0 else ts.topSize

/-- Set `errno`. -/
def setErrno (l : Local) (e : Nat) : Local := { l with thread := { l.thread with errno := e } }

/-- Replace the arena's tiling. -/
def withTiles (l : Local) (ts : TopSt) : Local := { l with av := { l.av with tiles := ts } }

/-- **`unlink_chunk`** of the chunk at `a` from the regular bin holding it (the unsorted bin or a
small/large bin), relabelled `u`. Aborts on a chunk in no regular bin. -/
def unlink (l : Local) (a : Nat) (u : Use) : Res Local :=
  match l.av.tiles.find? a with
  | some ⟨_, _, .bin 1⟩ =>
    .ok { l with av := { l.av with tiles := l.av.tiles.relabel a u, unsorted := l.av.unsorted.remove a } }
  | some ⟨_, _, .bin i⟩ => .ok (l.binRemove a i u)
  | _ => .error .corruptedDoubleLinked

/-- **Take the unsorted bin's last chunk** (`victim = unsorted_chunks (av)->bk` and its removal),
held `internal`. -/
def unsortedTake (l : Local) : Option (Nat × Local) :=
  (l.av.unsorted.takeLast).map fun (a, us) =>
    (a, { l with av := { l.av with tiles := l.av.tiles.relabel a .internal, unsorted := us } })

/-- **Split a held chunk, remainder to the unsorted bin's front**: the chunk at `a` becomes `nb`
bytes of use `u` and its remainder (at `a + nb`) is inserted at the head of the unsorted bin
(`_int_malloc`'s large-bin and bin-map paths). -/
def splitToUnsorted (l : Local) (a nb : Nat) (u : Use) : Local :=
  { l with av := { l.av with
      tiles := l.av.tiles.split a nb u (.bin 1)
      unsorted := l.av.unsorted.pushFront (a + nb) } }

/-- **Fuse** the chunk at `a` with the next one, as one chunk of use `u`. -/
def fuse (l : Local) (a : Nat) (u : Use) : Local := withTiles l (l.av.tiles.fuse a u)

/-- **Merge the current segment's last chunk into top.** -/
def mergeTop (l : Local) : Local := withTiles l l.av.tiles.mergeTop

/-- **Insert into a large bin** at glibc's position, binmap marked. -/
def largeInsert (l : Local) (a i : Nat) : Local :=
  { l with av := { l.av with
      tiles := l.av.tiles.relabel a (.bin i)
      bins := (l.av.bins.insertSorted l.av.tiles.sizeAt a i).mark i } }

/-- **Coalesce a held chunk and release it** (`_int_free_merge_chunk`'s body after its checks, and
`malloc_consolidate`'s inner step): merge backward with a free previous chunk, then into top if
the next chunk is top, else with a free next chunk, and insert the result at the head of the
unsorted bin. Returns glibc's `size` after `_int_free_create_chunk` (the merged chunk's size, or
the new top's size) for `_int_free_maybe_consolidate`. -/
def coalesce (l : Local) (a : Nat) : Res (Nat × Local) := do
  let some loc := l.av.tiles.locate a | .error .internal
  let (a, l) ← match loc.prev with
    | some pc =>
      if pc.use.tagFree then do
        let l ← unlink l pc.addr .internal
        pure (pc.addr, fuse l pc.addr .internal)
      else pure (a, l)
    | none => pure (a, l)
  let some loc := l.av.tiles.locate a | .error .internal
  match loc.next with
  | .top =>
    let l := mergeTop l
    pure (l.av.tiles.topSize, l)
  | .fence => pure (loc.self.size, l.unsortedPush a)
  | .chunk n =>
    if n.use.tagFree then do
      let l ← unlink l n.addr .internal
      let l := fuse l a .internal
      pure (loc.self.size + n.size, l.unsortedPush a)
    else pure (loc.self.size, l.unsortedPush a)

/-- Push a chunk `(addr, size)` on tcache bin `i` (thread only); the state is unchanged without a
tcache (unreachable: callers test for one). -/
def tcPut (l : Local) (c : Nat × Nat) (i : Nat) : Local := (l.tcachePut c i).getD l

/-- The count of tcache bin `i` (`tcache->counts[i]`; 0 without a tcache). -/
def tcCount (l : Local) (i : Nat) : Nat := (l.thread.tcache.map fun tc => (tc.bins i).length).getD 0

/-- The thread has a tcache and `i` is one of its bins. -/
def tcOn (l : Local) (i : Nat) : Bool := l.thread.tcache.isSome && decide (i < C.tcacheBins)

end Silmaril.Libc.Ptmalloc.Algo
