module

public import Silmaril.Wasm.SpecTec.Sim20.VecDer.Defs
public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Thms

/-!
# `simEnv20T B` and `simEnv20V B`: evaluation alike, typing alike off `vbad20`

* `envSameTV`: the evaluator cannot tell `simEnv20T B` and `simEnv20V B` apart (`VecAgree.envSameX`
  then `envSameV`).
* `typsOffB_vbad20` (kernel): every type of `fixedT20` outside `vbad20` unfolds to types outside
  `vbad20`. With the type tables, which agree off `instr`, `admininstr` and the three families,
  `typOffTV` is `ElseAgree.TypOff vbad20 (simEnv20T B) (simEnv20V B)`.
* **`hasTyp_offV_iff`**: in a scope without type variables, a type off `vbad20` types alike in both
  environments, in both directions.
* **`hasTyp_toV`**, `quantsOk_toV`: a harmless quantifier (`QuantV`) typed in `simEnv20T B` is
  typed in `simEnv20V B`: off `vbad20` by the above, at a `VOk` value by `VecAgree.hasTyp_TtoV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (QuantsOk)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (TypOff GoodT TypsOkT typsOffB goodT_of_all
  hasTyp_off_iff)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame find?_map_repl)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T fixedT20)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (simEnv20X fams envSameX envSameV simEnv20X_tables
  findTyp_off_simEnv20V hasTyp_TtoV)

/-! ## Evaluation -/

/-- `EnvSame` composes. -/
theorem envSame_trans {e₁ e₂ e₃ : Env} (h₁ : EnvSame e₁ e₂) (h₂ : EnvSame e₂ e₃) :
    EnvSame e₁ e₃ :=
  ⟨fun x => (h₂.defs x).trans (h₁.defs x), fun x => (h₂.rels x).trans (h₁.rels x),
    h₂.call.trans h₁.call, h₂.typV.trans h₁.typV, h₂.symV.trans h₁.symV, h₂.sub.trans h₁.sub⟩

/-- **`simEnv20T B` and `simEnv20V B` evaluate alike.** -/
theorem envSameTV (B : Builtins) : EnvSame (simEnv20T B) (simEnv20V B) :=
  envSame_trans (envSameX B) (envSameV B)

/-! ## Typing off `vbad20` -/

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Every type of `fixedT20` outside `vbad20` unfolds to types outside `vbad20`** (kernel). -/
theorem typsOffB_vbad20 : typsOffB vbad20 (typsOfDefs fixedT20) = true := by
  decide +kernel

/-- Off `instr` and `admininstr`, `simEnv20X B` has `simEnv20T B`'s types. -/
theorem findTyp_X_off (B : Builtins) {x : IL.Id} (hi : x ≠ "instr") (ha : x ≠ "admininstr") :
    (simEnv20X B).findTyp? x = (simEnv20T B).findTyp? x := by
  have ht := (simEnv20X_tables B).1
  simp only [Env.findTyp?, ht, find?_map_repl]
  simp [ha, hi]

/-- **The type tables of `simEnv20T B` and `simEnv20V B` agree off `vbad20`, which is closed.** -/
theorem typOffTV (B : Builtins) : TypOff vbad20 (simEnv20T B) (simEnv20V B) := by
  refine ⟨fun x hx => ?_, fun x td hx hd => ?_⟩
  · have hf : fams.contains x = false := by
      rcases hc : fams.contains x
      · rfl
      · simp [fams] at hc
        rcases hc with rfl | rfl | rfl <;> simp [vbad20] at hx
    have hi : x ≠ "instr" := by rintro rfl; simp [vbad20] at hx
    have ha : x ≠ "admininstr" := by rintro rfl; simp [vbad20] at hx
    exact (findTyp_off_simEnv20V B hf).trans (findTyp_X_off B hi ha)
  · have hm : (x, td) ∈ typsOfDefs fixedT20 := by
      have h' : (typsOfDefs fixedT20).find? x = some td := by
        simpa [simEnv20T, Env.withBuiltins, Env.findTyp?, envOfScript, envOfDefs_eq, Env.empty,
          Map.empty] using hd
      exact mem_of_find? h'
    have h := List.all_eq_true.1 typsOffB_vbad20 _ hm
    simp only [hx, Bool.false_or] at h
    intro i hi
    exact goodT_of_all (List.all_eq_true.1 h i hi)

/-- A scope without type variables. -/
theorem typsOkT_nilV {bad : List String} {ρ : VarEnv} (h : ρ.typs = []) : TypsOkT bad ρ := by
  intro p hp; rw [h] at hp; cases hp

/-- **Off `vbad20`, `simEnv20V B` types as `simEnv20T B`**, in both directions. -/
theorem hasTyp_offV_iff (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {t : Typ} {v : Value}
    (ht : GoodT vbad20 (evTyp t)) : HasTyp (simEnv20V B) ρ t v ↔ HasTyp (simEnv20T B) ρ t v :=
  hasTyp_off_iff (envSameTV B) (typOffTV B) (typsOkT_nilV hρ) ht

/-! ## Harmless quantifiers move forward -/

/-- **A harmless quantifier typed in `simEnv20T B` is typed in `simEnv20V B`.** -/
theorem hasTyp_toV {B : Builtins} {ρ : VarEnv} {t : Typ} {w : Value} (hρ : ρ.typs = [])
    (hq : QuantV ρ t w) (h : HasTyp (simEnv20T B) ρ t w) : HasTyp (simEnv20V B) ρ t w := by
  rcases hq with hoff | ⟨hv, ht⟩
  · exact (hasTyp_offV_iff B hρ hoff).2 h
  · refine hasTyp_TtoV (typsOkT_nilV hρ) ?_ ht hv h
    intro p hp; rw [hρ] at hp; cases hp

/-- **Harmless quantifiers typed in `simEnv20T B` are typed in `simEnv20V B`.** -/
theorem quantsOk_toV {B : Builtins} {ρ : VarEnv} {qs : List Param}
    (h : QuantsOk (simEnv20T B) ρ qs) (hv : QuantsV ρ qs) : QuantsOk (simEnv20V B) ρ qs :=
  fun x t hx =>
    let ⟨w, hw, ht⟩ := h x t hx
    ⟨w, hw, hasTyp_toV hv.1 (hv.2 x t w hx hw) ht⟩

end Silmaril.Wasm.SpecTec.Sim20.VecDer
