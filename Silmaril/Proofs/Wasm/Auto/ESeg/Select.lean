module

public import Silmaril.Proofs.Wasm.Auto.ESeg.LiftS

/-! # Soundness of the checkers with `select` and from function entry

* `segEquivSel_of_checkSegSel`, `bodyEquivSel_of_checkBodySel`: the checkers of
  `Silmaril.Wasm.Auto.ESeg` with `select` (`execS`);
* `eval_agree`: a term that reads only parameters has the same value in frames with the same
  parameters;
* `outEq_of₂`: the body argument of `Silmaril.Proofs.Wasm.Auto.ESeg.outEq_of` for two frames;
* **`funcEquiv_of_checkFunc`**: `checkFunc Γ da db rules a b c = true → FuncEquiv Γ da db a b`:
  bodies with different declared locals, compared from function entry.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg Silmaril.Wasm.Auto.XExec

/-- **Soundness of the segment checker with `select`.** -/
theorem segEquivSel_of_checkSegSel {Γ : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkSegSel Γ rules a b c = true) :
    SegEquivSel Γ a b := by
  simp only [checkSegSel, Bool.and_eq_true] at h
  obtain ⟨hl, h⟩ := h
  have hl' : Γ.length < 2 ^ 32 := by simpa [localsOk] using hl
  split at h
  · rename_i A B hA hB
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hst, hlo⟩, hcA⟩, hcB⟩ := h
    intro H s f rs hf
    rw [liftSel_exec hl' hA s rs hf, liftSel_exec hl' hB s rs hf,
      den_eq_of (evalL_eq_of_checkEqXL hR hf hst) (evalL_eq_of_checkEqXL hR hf hlo)
        (coversOk_sound hR hf · hcA) (coversOk_sound hR hf · hcB)]
  · cases h

/-- **Soundness of the body checker with `select`.** -/
theorem bodyEquivSel_of_checkBodySel {Γ : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkBodySel Γ rules a b c = true) :
    BodyEquivSel Γ a b := by
  simp only [checkBodySel, Bool.and_eq_true] at h
  obtain ⟨hl, h⟩ := h
  have hl' : Γ.length < 2 ^ 32 := by simpa [localsOk] using hl
  split at h
  · rename_i A B hA hB
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hst, hcA⟩, hcB⟩ := h
    intro H s f rs hf
    rw [liftSel_exec hl' hA s rs hf, liftSel_exec hl' hB s rs hf]
    exact outEq_of s rs (evalL_eq_of_checkEqXL hR hf hst) (coversOk_sound hR hf · hcA)
      (coversOk_sound hR hf · hcB)
  · cases h

/-! ## Function entry -/

/-- A term that reads only parameters has the same value in frames with the same
parameters. -/
theorem eval_agree {n : Nat} {fa fb : Frame} (hp : SameParams n fa fb) :
    ∀ {e : Term}, readsBelow n e = true → e.eval fa = e.eval fb
  | .const _ _, _ => rfl
  | .lget i, h => hp i (by simpa [readsBelow] using h)
  | .un t op a, h => by
    simp only [Term.eval, eval_agree hp (e := a) (by simpa [readsBelow] using h)]
  | .test t a, h => by
    simp only [Term.eval, eval_agree hp (e := a) (by simpa [readsBelow] using h)]
  | .bin t op a b, h => by
    simp only [readsBelow, Bool.and_eq_true] at h
    simp only [Term.eval, eval_agree hp h.1, eval_agree hp h.2]
  | .rel t op a b, h => by
    simp only [readsBelow, Bool.and_eq_true] at h
    simp only [Term.eval, eval_agree hp h.1, eval_agree hp h.2]

theorem evalL_agree {n : Nat} {fa fb : Frame} (hp : SameParams n fa fb) {es : List Term}
    (h : ∀ e ∈ es, readsBelow n e = true) : evalL fa es = evalL fb es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [evalL, eval_agree hp (h e (by simp)), ih (fun e' he' => h e' (by simp [he']))]

/-- Equal stacks and the same failures, in two frames of the same module, give results equal
up to the locals. -/
theorem outEq_of₂ {H : Type} {fa fb : Frame} {A B : Sym} (s : Store H) (rs : List Val)
    (hmod : fa.module = fb.module) (hst : evalL fa A.stack = evalL fb B.stack)
    (hA : (∀ e ∈ B.terms, (e.eval fb).isSome) → ∀ e ∈ A.terms, (e.eval fa).isSome)
    (hB : (∀ e ∈ A.terms, (e.eval fa).isSome) → ∀ e ∈ B.terms, (e.eval fb).isSome) :
    OutEq ((den fa A).map fun p => (s, p.1, p.2 ++ rs))
      ((den fb B).map fun p => (s, p.1, p.2 ++ rs)) := by
  by_cases hd : ∀ e ∈ A.terms, (e.eval fa).isSome
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (den_isSome_iff.mpr hd)
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (den_isSome_iff.mpr (hB hd))
    obtain ⟨_, ls, vs, -, -, hv, rfl⟩ := den_eq_some hp
    obtain ⟨_, ls', vs', -, -, hv', rfl⟩ := den_eq_some hq
    have hvs : vs = vs' := Option.some.inj (hv.symm.trans (hst.trans hv'))
    rw [hp, hq]
    exact ⟨rfl, hmod, by rw [hvs]⟩
  · have hnA : den fa A = none := by
      cases h : den fa A with
      | none => rfl
      | some p => exact absurd (den_isSome_iff.mp (by simp [h])) hd
    have hnB : den fb B = none := by
      cases h : den fb B with
      | none => rfl
      | some p => exact absurd (hA (den_isSome_iff.mp (by simp [h]))) hd
    rw [hnA, hnB]
    trivial

theorem frameOk_append_left {Γ ds : List IntType} {f : Frame} (h : FrameOk (Γ ++ ds) f) :
    FrameOk Γ f := fun i t hi => h i t (by rw [List.getElem?_append_left
      (List.getElem?_eq_some_iff.mp hi).1]; exact hi)

/-- **Soundness of the function checker.** -/
theorem funcEquiv_of_checkFunc {Γ da db : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkFunc Γ da db rules a b c = true) :
    FuncEquiv Γ da db a b := by
  simp only [checkFunc, Bool.and_eq_true] at h
  obtain ⟨⟨hla, hlb⟩, h⟩ := h
  have hla' : (Γ ++ da).length < 2 ^ 32 := by simpa [localsOk] using hla
  have hlb' : (Γ ++ db).length < 2 ^ 32 := by simpa [localsOk] using hlb
  split at h
  · show FuncEquiv Γ da db a b
    rename_i A B hA hB
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_append] at h
    obtain ⟨⟨⟨hbelow, hst⟩, hcA⟩, hcB⟩ := h
    intro H s fa fb rs hfa hfb hp hmod
    have hfb' : FrameOk Γ fb := frameOk_append_left hfb.1
    have hagA : ∀ e ∈ A.terms, e.eval fa = e.eval fb :=
      fun e he => eval_agree hp (hbelow e (.inl he))
    have hstA : evalL fa A.stack = evalL fb A.stack :=
      evalL_agree hp fun e he => hbelow e (.inl (by simp [Sym.terms, he]))
    rw [liftEntrySel_exec hla' hA s rs hfa, liftEntrySel_exec hlb' hB s rs hfb]
    refine outEq_of₂ s rs hmod (hstA.trans (evalL_eq_of_checkEqXL hR hfb' hst)) ?_ ?_
    · intro hB' e he
      rw [hagA e he]
      exact coversOk_sound hR hfb' hB' hcA e he
    · intro hA' e he
      exact coversOk_sound hR hfb' (fun e' he' => by rw [← hagA e' he']; exact hA' e' he') hcB e he
  · cases h

end Silmaril.Proofs.Wasm.Auto.ESeg
