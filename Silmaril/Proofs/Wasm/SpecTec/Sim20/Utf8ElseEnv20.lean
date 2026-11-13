module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseEnv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseClean20

/-!
# `simEnv20 B` and `utf8Env20 B`: the other 2.0 pair

The forward invariant `StoreBulk.Good20B` reads its typing in `simEnv20 B` (the 2.0 script
without the `STORE` erratum), and `Utf8Mono.Good20BU` in `utf8Env20 B`. The converse
monotonicity of this topic applies to that pair too:

* `refFree20`, **`clean20`**: in `Scripts.Wasm20.fixed` only `$utf8`, `name` and `Bname` refer to
  `$utf8` (kernel), so `simEnv20 B` is `Clean` at `$utf8`. Hence `simEnv20 B` and `utf8Env20 B`
  evaluate alike away from `$utf8` (`evalExp_iff` with `Utf8Mono.envExt20`).
* `typsOffB_badU20S`: `badU20` is closed in `Scripts.Wasm20.fixed` as well (kernel).
* **`hasTyp_u20_iff`**: in a scope without type variables, a type off `badU20` that never refers to
  `$utf8` types alike in `utf8Env20 B` and `simEnv20 B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evTyp evInst mem_of_find? typDefEv
  findTyp?_envOfScript_item)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (TypOff GoodT TypsOkT typsOffB goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (envExt20 findTyp?_utf8Env20)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **`badU20` is closed in the 2.0 script** (kernel). -/
theorem typsOffB_badU20S : typsOffB badU20 (typsOfDefs Scripts.Wasm20.fixed) = true := by
  decide +kernel

/-- **The type tables of `simEnv20 B` and `utf8Env20 B` agree, and `badU20` is closed.** -/
theorem typOffU20 (B : Builtins) : TypOff badU20 (simEnv20 B) (utf8Env20 B) := by
  refine ⟨fun x _ => findTyp?_utf8Env20 B x, fun x td hx hd => ?_⟩
  have hm : (x, td) ∈ typsOfDefs Scripts.Wasm20.fixed := by
    have h' : (typsOfDefs Scripts.Wasm20.fixed).find? x = some td := by
      simpa [simEnv20, baseEnv20, Env.withBuiltins, Env.findTyp?, envOfScript, envOfDefs_eq,
        Env.empty, Map.empty] using hd
    exact mem_of_find? h'
  have h := List.all_eq_true.1 typsOffB_badU20S _ hm
  simp only [hx, Bool.false_or] at h
  intro i hi
  exact goodT_of_all (List.all_eq_true.1 h i hi)

/-- **No type of the 2.0 script outside `badU20` refers to `$utf8`.** -/
theorem typFreeOff20 (B : Builtins) : TypFreeOff badU20 (simEnv20 B) "utf8" := by
  intro x td hx hd i hi
  have hd' : (envOfScript Scripts.Wasm20.fixed).findTyp? x = some td := by
    simpa [simEnv20, baseEnv20, Env.withBuiltins, Env.findTyp?] using hd
  have hxn : x ≠ "name" := by rintro rfl; simp [badU20] at hx
  have hG := goodEvs_of_refFree refFree20 (findTyp?_envOfScript_item hd')
    (by simp [utf8Users20, hxn])
  simp only [typDefEv, goodEvs_append, goodEvs_flatMap] at hG
  exact hG.2 i hi

/-- **Off `badU20` and `$utf8`, `utf8Env20 B` types as `simEnv20 B`.** -/
theorem hasTyp_u20_iff {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv}
    (hρ : ρ.typs = []) (hD : DefsOk "utf8" ρ) {t : Typ} {v : Value}
    (ht : GoodT badU20 (evTyp t)) (hte : GoodEvs "utf8" (evTyp t)) :
    HasTyp (utf8Env20 B) ρ t v ↔ HasTyp (simEnv20 B) ρ t v :=
  hasTyp_iff (envExt20 B hB) (clean20 B) (typOffU20 B) (typFreeOff20 B) hD (typsOkT_nilU hρ)
    (typsEv_nil hρ) ht hte

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
