module

public import Silmaril.Libc.Ptmalloc.Algo.Defs
public import Silmaril.Libc.Alloc.Defs

/-!
# ptmalloc: refinement of the allocator institution, at the algorithm level

The allocator institution's abstract level (`Silmaril.Libc.AllocInst`:
`AbsAlloc`, `AbsAlloc.SatOn F P Inv allocLoose`) judges an allocator by the **visible heap of
ownership tokens** `Heap` (block start ↦ requested size) of `Silmaril.Libc.Alloc`.
This module gives the algorithm model that reading, with **ghost tokens**:

* `TokSt`: a `World` and the token heap `h` (the requested sizes, which ptmalloc forgets);
* `TokensMatch C w h`: the tokens are exactly the live payloads of `World.live`, each token's
  size at most the payload's usable size;
* `absStep C A tid`: one call of thread `tid` (`malloc`, `free`, a client `access`); a `free` of a
  non-token is a safety violation (`none`) whatever the model would do (glibc aborts or
  corrupts), every other call is the model's.
* `SafeMF C A tid Inv`: the fields of `AbsAlloc.SatOn Frag.mf (fun _ => True) Inv allocLoose`
  for the abstract allocator `(TokSt, (·.h), absStep)`, written out (AI1's `AbsAlloc` is not on
  main yet; once it is, `absAlloc C A tid` and `SafeMF ↔ SatOn` are a few lines).

The reduction `Algo.safeMF_of_tasks` (`Silmaril.Libc.Ptmalloc.Refine.Thms`) proves `SafeMF` from the
world-level obligations of `Silmaril.Libc.Ptmalloc.Algo.Defs` (`Task.algo.wfWorld`,
`Task.algo.mallocTotal`) and the two below (`Task.algo.liveApart`: well-formed worlds have
disjoint, bounded live payloads; `Task.algo.tidsKept`), for **any** `A : Ops C`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

open Silmaril.Libc

/-- The algorithm state with the ghost token heap. -/
structure TokSt where
  w : World
  h : Heap

/-- **The tokens are the live payloads**, each token's requested size within the usable size. -/
def TokensMatch (C : Config) (w : World) (h : Heap) : Prop :=
  (∀ p n, h p = some n → ∃ u, (p, u) ∈ w.live C ∧ n ≤ u) ∧
    ∀ p u, (p, u) ∈ w.live C → ∃ n, h p = some n

/-- Live payloads pairwise disjoint, non-null, non-empty and below `2 ^ 64`. -/
def LiveApart (live : List (Nat × Nat)) : Prop :=
  live.Pairwise (fun q r => q.1 + q.2 ≤ r.1 ∨ r.1 + r.2 ≤ q.1) ∧
    ∀ q ∈ live, q.1 ≠ 0 ∧ 0 < q.2 ∧ q.1 + q.2 ≤ 2 ^ 64

/-- The calls of the `malloc`/`free` fragment (with client accesses): `ACall.In Frag.mf`. -/
def InMF : ACall → Prop
  | .malloc _ | .free _ | .access _ => True
  | _ => False

/-- **One call of thread `tid`**, with ghost tokens. -/
def absStep (C : Config) (A : Ops C) (tid : Nat) (s : TokSt) : ACall → Option (TokSt × Nat) → Prop
  | .malloc n, o => ∃ p w', A.malloc s.w tid n = .ok (p, w') ∧
      o = some (⟨w', if p = 0 then s.h else s.h.add p n⟩, p)
  | .free p, o =>
    if p = 0 then o = some (s, 0) else
    match s.h p with
    | none => o = none
    | some _ => ∃ w', A.free s.w tid p = .ok w' ∧ o = some (⟨w', s.h.remove p⟩, 0)
  | .access p, o => (s.h.Owns p ∧ o = some (s, 0)) ∨ (¬ s.h.Owns p ∧ o = none)
  | _, o => o = none

/-- The visible outcome. -/
def absOut : Option (TokSt × Nat) → AOut
  | none => .ub
  | some (t, r) => .ok t.h r

/-- **`AbsAlloc.SatOn Frag.mf (fun _ => True) Inv allocLoose`** for the token reading of `A`
(thread `tid`, load-time world `w0`), written out. -/
structure SafeMF (C : Config) (A : Ops C) (tid : Nat) (w0 : World) (Inv : TokSt → Prop) : Prop where
  init : Inv ⟨w0, Heap.empty⟩
  rel : ∀ s c o, Inv s → InMF c → absStep C A tid s c o → allocLoose s.h c (absOut o)
  inv : ∀ s c t r, Inv s → InMF c → absStep C A tid s c (some (t, r)) → Inv t
  progress : ∀ s c, Inv s → InMF c → ∃ o, absStep C A tid s c o

/-- **`Task.algo.liveApart`**: on a well-formed world the live payloads are apart and bounded
(the spatial content of `WorldWF`: tilings, segments, `mmap`ed chunks and the kernel's regions
are disjoint). -/
def Task.algo.liveApart (C : Config) : Prop :=
  C.Ok → ∀ w, WorldWF C w → LiveApart (w.live C)

/-- **`Task.algo.tidsKept`**: `malloc` and `free` keep the set of threads. -/
def Task.algo.tidsKept (C : Config) (A : Ops C) : Prop :=
  C.Ok → ∀ w tid, WorldWF C w → tid ∈ w.tids →
    (∀ n p w', A.malloc w tid n = .ok (p, w') → w'.tids = w.tids) ∧
    (∀ p w', A.free w tid p = .ok w' → w'.tids = w.tids)

/-- **`Task.algo.mallocLive`** (the `live` strength at the algorithm level): `malloc` fails only
when the request is too large or the kernel was asked (and so may have refused); never
spuriously. -/
def Task.algo.mallocLive (C : Config) (A : Ops C) : Prop :=
  C.Ok → ∀ w tid n w', WorldWF C w → tid ∈ w.tids → A.malloc w tid n = .ok (0, w') →
    C.checkedRequest2size n = none ∨ w.kernel.asked < w'.kernel.asked

end Silmaril.Libc.Ptmalloc.Algo
