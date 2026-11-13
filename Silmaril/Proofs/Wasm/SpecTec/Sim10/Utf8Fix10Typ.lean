module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Clean

/-!
# The 1.0 `$utf8` erratum: what never refers to `$utf8` types alike

* `typsOffB_badU10` (kernel): every type of `fixedT10` outside `Utf8Else.badU20` unfolds to types
  outside it. The 2.0 list is closed in `fixedT10` as well.
* **`hasTyp_u10T_iff`**: in a scope without type variables, a type that avoids those twelve
  types and `$utf8` types alike in `utf8Env10T B` and `simEnv10T B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp mem_of_find? typDefEv
  findTyp?_envOfScript_item)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (TypOff GoodT typsOffB goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (refFreeB utf8Users20 badU20 Clean clean_of_refFree
  TypFreeOff goodEvs_of_refFree goodEvs_append goodEvs_flatMap DefsOk GoodEvs hasTyp_iff
  typsOkT_nilU typsEv_nil)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T fixedT10)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Every type of `fixedT10` outside `badU20` unfolds to types outside `badU20`** (kernel). -/
theorem typsOffB_badU10 : typsOffB badU20 (typsOfDefs fixedT10) = true := by
  decide +kernel

/-- **The type tables of `simEnv10T B` and `utf8Env10T B` agree, and `badU20` is closed.** -/
theorem typOffU10T (B : Builtins) : TypOff badU20 (simEnv10T B) (utf8Env10T B) := by
  refine ⟨fun x _ => findTyp?_utf8Env10T B x, fun x td hx hd => ?_⟩
  have hm : (x, td) ∈ typsOfDefs fixedT10 := by
    have h' : (typsOfDefs fixedT10).find? x = some td := by
      simpa [simEnv10T, Env.withBuiltins, Env.findTyp?, envOfScript, envOfDefs_eq, Env.empty,
        Map.empty] using hd
    exact mem_of_find? h'
  have h := List.all_eq_true.1 typsOffB_badU10 _ hm
  simp only [hx, Bool.false_or] at h
  intro i hi
  exact goodT_of_all (List.all_eq_true.1 h i hi)

/-- **No type of `fixedT10` outside `badU20` refers to `$utf8`.** -/
theorem typFreeOff10T (B : Builtins) : TypFreeOff badU20 (simEnv10T B) "utf8" := by
  intro x td hx hd i hi
  have hd' : (envOfScript fixedT10).findTyp? x = some td := by
    simpa [simEnv10T, Env.withBuiltins, Env.findTyp?] using hd
  have hxn : x ≠ "name" := by rintro rfl; simp [badU20] at hx
  have hG := goodEvs_of_refFree refFree10T (findTyp?_envOfScript_item hd')
    (by simp [utf8Users20, hxn])
  simp only [typDefEv, goodEvs_append, goodEvs_flatMap] at hG
  exact hG.2 i hi

/-- **Off the twelve types that reach `name` and off `$utf8`, `utf8Env10T B` types as
`simEnv10T B`.** -/
theorem hasTyp_u10T_iff {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv}
    (hρ : ρ.typs = []) (hD : DefsOk "utf8" ρ) {t : Typ} {v : Value}
    (ht : GoodT badU20 (evTyp t)) (hte : GoodEvs "utf8" (evTyp t)) :
    HasTyp (utf8Env10T B) ρ t v ↔ HasTyp (simEnv10T B) ρ t v :=
  hasTyp_iff (envExt10T B hB) (clean10T B) (typOffU10T B) (typFreeOff10T B) hD (typsOkT_nilU hρ)
    (typsEv_nil hρ) ht hte

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix
