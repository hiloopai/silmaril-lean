module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseMove

/-!
# `simEnv20T B` and `utf8Env20T B`: typing off the types that reach `name`

The 2.0 instance of `Raw/…/Utf8Else/Typ.lean`:

* `typsOffB_badU20`: every type of `fixedT20` outside `badU20` unfolds to types outside `badU20`
  (kernel). With the shared type tables, `typOffU20T` is `ElseAgree.TypOff badU20 (simEnv20T B)
  (utf8Env20T B)`.
* `typFreeOff20T`: no type of `fixedT20` outside `badU20` refers to `$utf8`. `name` is in
  `badU20`, so this follows from `refFree20T`.
* **`hasTyp_u20T_iff`**: in a scope without type variables, a type that avoids `badU20` and
  `$utf8` types alike in `utf8Env20T B` and `simEnv20T B`, for `B` that leaves `$utf8`
  uninterpreted.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evTyp evInst mem_of_find? typDefEv
  findTyp?_envOfScript_item)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (TypOff GoodT TypsOkT typsOffB goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T fixedT20)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T envExt20T findTyp?_utf8Env20T)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Every type of `fixedT20` outside `badU20` unfolds to types outside `badU20`** (kernel). -/
theorem typsOffB_badU20 : typsOffB badU20 (typsOfDefs fixedT20) = true := by
  decide +kernel

/-- **The type tables of `simEnv20T B` and `utf8Env20T B` agree, and `badU20` is closed.** -/
theorem typOffU20T (B : Builtins) : TypOff badU20 (simEnv20T B) (utf8Env20T B) := by
  refine ⟨fun x _ => findTyp?_utf8Env20T B x, fun x td hx hd => ?_⟩
  have hm : (x, td) ∈ typsOfDefs fixedT20 := by
    have h' : (typsOfDefs fixedT20).find? x = some td := by
      simpa [simEnv20T, Env.withBuiltins, Env.findTyp?, envOfScript, envOfDefs_eq, Env.empty,
        Map.empty] using hd
    exact mem_of_find? h'
  have h := List.all_eq_true.1 typsOffB_badU20 _ hm
  simp only [hx, Bool.false_or] at h
  intro i hi
  exact goodT_of_all (List.all_eq_true.1 h i hi)

/-- **No type of `fixedT20` outside `badU20` refers to `$utf8`.** -/
theorem typFreeOff20T (B : Builtins) : TypFreeOff badU20 (simEnv20T B) "utf8" := by
  intro x td hx hd i hi
  have hd' : (envOfScript fixedT20).findTyp? x = some td := by
    simpa [simEnv20T, Env.withBuiltins, Env.findTyp?] using hd
  have hxn : x ≠ "name" := by rintro rfl; simp [badU20] at hx
  have hG := goodEvs_of_refFree refFree20T (findTyp?_envOfScript_item hd')
    (by simp [utf8Users20, hxn])
  simp only [typDefEv, goodEvs_append, goodEvs_flatMap] at hG
  exact hG.2 i hi

/-- A scope without type variables. -/
theorem typsOkT_nilU {ρ : VarEnv} (h : ρ.typs = []) : TypsOkT badU20 ρ := by
  intro p hp; rw [h] at hp; cases hp

theorem typsEv_nil {x₀ : String} {ρ : VarEnv} (h : ρ.typs = []) : TypsEv x₀ ρ := by
  intro p hp; rw [h] at hp; cases hp

/-- **Off `badU20` and `$utf8`, `utf8Env20T B` types as `simEnv20T B`.** -/
theorem hasTyp_u20T_iff {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv}
    (hρ : ρ.typs = []) (hD : DefsOk "utf8" ρ) {t : Typ} {v : Value}
    (ht : GoodT badU20 (evTyp t)) (hte : GoodEvs "utf8" (evTyp t)) :
    HasTyp (utf8Env20T B) ρ t v ↔ HasTyp (simEnv20T B) ρ t v :=
  hasTyp_iff (envExt20T B hB) (clean20T B) (typOffU20T B) (typFreeOff20T B) hD (typsOkT_nilU hρ)
    (typsEv_nil hρ) ht hte

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
