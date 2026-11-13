module

public import Silmaril.Proofs.Wasm.Models.FXPres.Typing

/-!
# `TL` covers the straight-line judgement `TypedFX`

`typedFX_TL`: with value types read as themselves (`ι = .val`), the frame's module `m₀` and a
Core typing `ct` that contains `TypedFX`'s parameter `core` (on instructions other than `br`
and `return`), every `TypedFX` derivation is a `TL` derivation, under any labels, return type,
store and slot typing. Two side conditions record where `TL` checks more than `TypedFX`:
`cont.new` (its operand is checked against `newTy`) and the handler clauses of `resume` (they
must fit the labels); the code here has no `cont.new` and resumes with no clauses.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres

variable {H : Type} {E : TyEnv H} {s : Store H} {Γ : List TypeIdx}
  {Ls : List (List FTy)} {R : Option (List FTy)}

/-- Straight-line code that `TL` and `TypedFX` check alike. -/
def PlainFX (is : List InstrFX) : Prop :=
  ∀ x ∈ is, (∀ ct, x ≠ .fx (.contNew ct)) ∧ ∀ ct hs, x = .fx (.resume ct hs) → hs = []

theorem tys_val (hι : E.ι = FTy.val) (ts : List CValType) : E.tys ts = vtys ts := by
  simp [TyEnv.tys, vtys, hι]

theorem TL.bind_vtys (hι : E.ι = FTy.val) {ct ct' : TypeIdx} {ps₁ ps₂ rs : List CValType}
    (h : contType? E.m₀ ct = some (ps₁ ++ ps₂, rs)) (h' : contType? E.m₀ ct' = some (ps₂, rs)) :
    TL E s Γ Ls R [InstrFX.toAdmin (.fx (.contBind ct ct'))] (vtys ps₁ ++ [.cont ct])
      [.cont ct'] := by
  simpa [InstrFX.toAdmin, tys_val hι] using
    (TL.contBind (s := s) (Γ := Γ) (Ls := Ls) (R := R) (pre := []) h h' .nil)

theorem TL.resume_vtys (hι : E.ι = FTy.val) {ct : TypeIdx} {ps rs : List CValType}
    (h : contType? E.m₀ ct = some (ps, rs)) :
    TL E s Γ Ls R [InstrFX.toAdmin (.fx (.resume ct []))] (vtys ps ++ [.cont ct]) (vtys rs) := by
  simpa [InstrFX.toAdmin, tys_val hι] using
    (TL.resume (s := s) (Γ := Γ) (Ls := Ls) (R := R) (pre := []) (hs := []) h
      (fun c hc => by simp at hc) .nil)

/-- **`TL` covers `TypedFX`.** -/
theorem typedFX_TL {core : Instr → List CValType → List CValType → Prop} (hι : E.ι = FTy.val)
    (hcore : ∀ {i t₁ t₂}, core i t₁ t₂ →
      E.ct s (.plain i) (vtys t₁) (vtys t₂) ∧ ¬ IsCtl (.plain i))
    {is : List InstrFX} {t₁ t₂ : List FTy} (h : TypedFX core E.m₀ is t₁ t₂) (hp : PlainFX is) :
    TL E s Γ Ls R (is.map InstrFX.toAdmin) t₁ t₂ := by
  induction h with
  | nil => exact .nil
  | core hc =>
    obtain ⟨hct, hn⟩ := hcore hc
    simpa [InstrFX.toAdmin] using TL.core (pre := []) hct hn .nil
  | contNew => exact absurd rfl ((hp _ (List.mem_singleton_self _)).1 _)
  | contBind h h' => exact TL.bind_vtys hι h h'
  | @resume ct hs ps rs h =>
    have hs0 : hs = [] := (hp _ (List.mem_singleton_self _)).2 ct hs rfl
    exact hs0 ▸ TL.resume_vtys hι h
  | append _ _ ih₁ ih₂ =>
    rw [List.map_append]
    exact TL.append (ih₁ fun x hx => hp x (List.mem_append_left _ hx))
      (ih₂ fun x hx => hp x (List.mem_append_right _ hx))
  | frame ts _ ih => exact TL.weaken ts (ih hp)

end Silmaril.Proofs.Wasm.Models.FXPres
