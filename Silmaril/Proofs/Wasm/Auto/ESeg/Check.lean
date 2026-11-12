module

public import Silmaril.Raw.Wasm.Auto.ESeg.Lift

/-! # Soundness of the segment and body checkers

* `den_isSome_iff`: a summary denotes a result exactly when all its terms have values;
* `den_eq_of`, `outEq_of`: equal stacks (and locals), and covers both ways, give equal
  denotations (results equal up to the locals);
* **`segEquiv_of_checkSeg`**: `checkSeg Γ rules a b c = true → SegEquiv Γ a b`, the exec-level
  segment equivalence of `Silmaril.Wasm.Auto.EGraph` (same store, frame, stack and failures), for
  code with `local.set`, `local.tee` and `drop`;
* **`bodyEquiv_of_checkBody`**: `checkBody Γ rules a b c = true → BodyEquiv Γ a b`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph

variable {f : Frame}

theorem evalL_isSome_iff {es : List Term} :
    (evalL f es).isSome ↔ ∀ e ∈ es, (e.eval f).isSome := by
  have h := evalL_none_iff (f := f) (es := es)
  constructor
  · intro hs e he
    cases hv : e.eval f with
    | none => rw [h.mpr ⟨e, he, hv⟩] at hs; cases hs
    | some _ => rfl
  · intro ha
    cases hv : evalL f es with
    | none =>
      obtain ⟨e, he, hn⟩ := h.mp hv
      have := ha e he
      rw [hn] at this; cases this
    | some _ => rfl

/-- A summary denotes a result exactly when every term has a value. -/
theorem den_isSome_iff {S : Sym} : (den f S).isSome ↔ ∀ e ∈ S.terms, (e.eval f).isSome := by
  have hG := evalL_isSome_iff (f := f) (es := S.guards)
  have hL := evalL_isSome_iff (f := f) (es := S.locs)
  have hS := evalL_isSome_iff (f := f) (es := S.stack)
  simp only [Sym.terms, List.mem_append]
  constructor
  · intro h e he
    cases hg : evalL f S.guards <;> cases hl : evalL f S.locs <;> cases hs : evalL f S.stack <;>
      simp [den, hg, hl, hs] at h
    rcases he with (he | he) | he
    · exact hG.mp (by simp [hg]) e he
    · exact hL.mp (by simp [hl]) e he
    · exact hS.mp (by simp [hs]) e he
  · intro h
    obtain ⟨gs, hg⟩ := Option.isSome_iff_exists.mp (hG.mpr fun e he => h e (.inl (.inl he)))
    obtain ⟨ls, hl⟩ := Option.isSome_iff_exists.mp (hL.mpr fun e he => h e (.inl (.inr he)))
    obtain ⟨vs, hs⟩ := Option.isSome_iff_exists.mp (hS.mpr fun e he => h e (.inr he))
    simp [den, hg, hl, hs]

/-- Equal stacks and locals, and the same failures, give the same denotation. -/
theorem den_eq_of {A B : Sym} (hst : evalL f A.stack = evalL f B.stack)
    (hlo : evalL f A.locs = evalL f B.locs)
    (hA : (∀ e ∈ B.terms, (e.eval f).isSome) → ∀ e ∈ A.terms, (e.eval f).isSome)
    (hB : (∀ e ∈ A.terms, (e.eval f).isSome) → ∀ e ∈ B.terms, (e.eval f).isSome) :
    den f A = den f B := by
  by_cases hd : ∀ e ∈ A.terms, (e.eval f).isSome
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (den_isSome_iff.mpr hd)
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (den_isSome_iff.mpr (hB hd))
    obtain ⟨_, ls, vs, -, hl, hv, rfl⟩ := den_eq_some hp
    obtain ⟨_, ls', vs', -, hl', hv', rfl⟩ := den_eq_some hq
    have hls : ls = ls' := Option.some.inj (hl.symm.trans (hlo.trans hl'))
    have hvs : vs = vs' := Option.some.inj (hv.symm.trans (hst.trans hv'))
    rw [hp, hq, hls, hvs]
  · have hnA : den f A = none := by
      cases h : den f A with
      | none => rfl
      | some p => exact absurd (den_isSome_iff.mp (by simp [h])) hd
    have hnB : den f B = none := by
      cases h : den f B with
      | none => rfl
      | some p => exact absurd (hA (den_isSome_iff.mp (by simp [h]))) hd
    rw [hnA, hnB]

/-- Equal stacks and the same failures give results equal up to the locals. -/
theorem outEq_of {H : Type} {A B : Sym} (s : Store H) (rs : List Val)
    (hst : evalL f A.stack = evalL f B.stack)
    (hA : (∀ e ∈ B.terms, (e.eval f).isSome) → ∀ e ∈ A.terms, (e.eval f).isSome)
    (hB : (∀ e ∈ A.terms, (e.eval f).isSome) → ∀ e ∈ B.terms, (e.eval f).isSome) :
    OutEq ((den f A).map fun p => (s, p.1, p.2 ++ rs)) ((den f B).map fun p => (s, p.1, p.2 ++ rs)) := by
  by_cases hd : ∀ e ∈ A.terms, (e.eval f).isSome
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (den_isSome_iff.mpr hd)
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (den_isSome_iff.mpr (hB hd))
    obtain ⟨_, ls, vs, -, -, hv, rfl⟩ := den_eq_some hp
    obtain ⟨_, ls', vs', -, -, hv', rfl⟩ := den_eq_some hq
    have hvs : vs = vs' := Option.some.inj (hv.symm.trans (hst.trans hv'))
    rw [hp, hq]
    exact ⟨rfl, rfl, by rw [hvs]⟩
  · have hnA : den f A = none := by
      cases h : den f A with
      | none => rfl
      | some p => exact absurd (den_isSome_iff.mp (by simp [h])) hd
    have hnB : den f B = none := by
      cases h : den f B with
      | none => rfl
      | some p => exact absurd (hA (den_isSome_iff.mp (by simp [h]))) hd
    rw [hnA, hnB]
    trivial

/-- **Soundness of the segment checker.** -/
theorem segEquiv_of_checkSeg {Γ : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkSeg Γ rules a b c = true) :
    SegEquiv Γ a b := by
  simp only [checkSeg, Bool.and_eq_true] at h
  obtain ⟨hl, h⟩ := h
  have hl' : Γ.length < 2 ^ 32 := by simpa [localsOk] using hl
  split at h
  · rename_i A B hA hB
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hst, hlo⟩, hcA⟩, hcB⟩ := h
    intro H s f rs hf
    rw [lift_exec hl' hA s rs hf, lift_exec hl' hB s rs hf,
      den_eq_of (evalL_eq_of_checkEqXL hR hf hst) (evalL_eq_of_checkEqXL hR hf hlo)
        (coversOk_sound hR hf · hcA) (coversOk_sound hR hf · hcB)]
  · cases h

/-- **Soundness of the body checker.** -/
theorem bodyEquiv_of_checkBody {Γ : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkBody Γ rules a b c = true) :
    BodyEquiv Γ a b := by
  simp only [checkBody, Bool.and_eq_true] at h
  obtain ⟨hl, h⟩ := h
  have hl' : Γ.length < 2 ^ 32 := by simpa [localsOk] using hl
  split at h
  · rename_i A B hA hB
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hst, hcA⟩, hcB⟩ := h
    intro H s f rs hf
    rw [lift_exec hl' hA s rs hf, lift_exec hl' hB s rs hf]
    exact outEq_of s rs (evalL_eq_of_checkEqXL hR hf hst) (coversOk_sound hR hf · hcA)
      (coversOk_sound hR hf · hcB)
  · cases h

end Silmaril.Proofs.Wasm.Auto.ESeg