module

public import Silmaril.Proofs.Wasm.Auto.Equiv.Check

/-!
# Equivalence on typed concrete states

`SegEquiv` is stated over the frames and stacks that a symbolic initial state denotes.
Every concrete frame whose locals are integer values of the types `lt`, with integer values
of the types `st` on top of the stack, is one of them (`frameAt_envOfVals`,
`stackAt_envOfVals`), so `SegEquiv.typed`/`OutEquiv.typed` apply to any typed configuration,
for instance one that validation guarantees.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Wp Corr)

theorem asBV_num (t : IntType) (x : BitVec t.width) : asBV t (.num ⟨.int t, x⟩) = x := by
  cases t <;> rfl

theorem den_envOfVals {ts : List IntType} {vs : List Val} (htv : TypedVals ts vs)
    (rest more : List Val) (i : Nat) (hi : i < ts.length) :
    den (envOfVals (rest ++ vs ++ more)) (ts[i], .var (rest.length + i)) =
      vs[i]'(htv.1 ▸ hi) := by
  obtain ⟨x, hx⟩ := htv.2 i hi
  have hget : (rest ++ vs ++ more).getD (rest.length + i) (Val.i32 0) = vs[i]'(htv.1 ▸ hi) := by
    rw [List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (htv.1 ▸ hi), List.getElem?_eq_getElem (htv.1 ▸ hi)]
    rfl
  simp only [den, ev, envOfVals, hget, hx, asBV_num]

theorem map_den_envOfVals {ts : List IntType} {vs : List Val} (htv : TypedVals ts vs)
    (rest more : List Val) :
    (ts.mapIdx fun i t => (t, Term.var (rest.length + i))).map
      (den (envOfVals (rest ++ vs ++ more))) = vs := by
  apply List.ext_getElem
  · simp [htv.1]
  · intro i h₁ h₂
    have hi : i < ts.length := by simpa using h₁
    have h : den (envOfVals (rest ++ vs ++ more)) (ts[i], .var (rest.length + i)) =
        vs[i]'(htv.1 ▸ hi) := den_envOfVals htv rest more i hi
    simpa using h

theorem stackAt_envOfVals {lt st : List IntType} {ls rs : List Val} (hl : TypedVals lt ls)
    (hs : TypedVals st rs) : stackAt (envOfVals (ls ++ rs)) (initState lt st) = rs := by
  have h := map_den_envOfVals hs ls []
  simpa [stackAt, initState, hl.1] using h

theorem locals_envOfVals {lt : List IntType} {ls : List Val} (hl : TypedVals lt ls)
    (rs : List Val) :
    (lt.mapIdx fun i t => (t, Term.var i)).map (den (envOfVals (ls ++ rs))) = ls := by
  have h := map_den_envOfVals hl [] rs
  simpa using h

theorem frameAt_envOfVals {lt st : List IntType} {ls rs : List Val} {f : Frame}
    (hf : f.locals = ls.map some) (hl : TypedVals lt ls) :
    frameAt f (envOfVals (ls ++ rs)) (initState lt st) = f := by
  have h := locals_envOfVals hl rs
  have h' : (lt.mapIdx fun i t => (t, Term.var i)).map
      (fun p => some (den (envOfVals (ls ++ rs)) p)) = f.locals := by
    rw [hf]
    conv => rhs; rw [← h]
    rw [List.map_map]
    rfl
  rcases f with ⟨locals, module⟩
  simp only [frameAt, initState]
  simp only at h'
  rw [h']

/-- **`SegEquiv` on typed concrete states.** -/
theorem SegEquiv.typed {lt st : List IntType} {a b : List Instr} (h : SegEquiv lt st a b)
    (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) {f : Frame}
    {ls rs : List Val} (hf : f.locals = ls.map some) (hl : TypedVals lt ls)
    (hs : TypedVals st rs) (us : List Val) (rest : List Admin)
    (Q : Silmaril.Wasm.Logic.Core.Post H) :
    Wp m P host s f (vals (us ++ rs.reverse) ++ expression a ++ rest) Q ↔
      Wp m P host s f (vals (us ++ rs.reverse) ++ expression b ++ rest) Q := by
  have h₁ := h m P host s f (envOfVals (ls ++ rs)) us rest Q
  rw [frameAt_envOfVals hf hl] at h₁
  simpa [codeAt, stackAt_envOfVals hl hs] using h₁

/-- **`OutEquiv` on typed concrete states.** -/
theorem OutEquiv.typed {lt st : List IntType} {a b : List Instr} (h : OutEquiv lt st a b)
    (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) {f : Frame}
    {ls rs : List Val} (hf : f.locals = ls.map some) (hl : TypedVals lt ls)
    (hs : TypedVals st rs) (us : List Val) (Q : Silmaril.Wasm.Logic.Core.Post H)
    (hQ : LocalsBlind Q) :
    Wp m P host s f (vals (us ++ rs.reverse) ++ expression a) Q ↔
      Wp m P host s f (vals (us ++ rs.reverse) ++ expression b) Q := by
  have h₁ := h m P host s f (envOfVals (ls ++ rs)) us Q hQ
  rw [frameAt_envOfVals hf hl] at h₁
  simpa [codeAt, stackAt_envOfVals hl hs] using h₁

end Silmaril.Proofs.Wasm.Auto.Equiv