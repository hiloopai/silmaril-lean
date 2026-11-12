module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreFix10

/-!
# The 1.0 `STORE` erratum types `STORE`

By evaluation of `hasTyp` in `simEnv10T`, at every builtins: `i32.store`, `i64.store8` and
`f32.store` are typed `admininstr`s (`typedV_i32Store10T`, …), and a packed float store is still
rejected (`storeCaseFix10_rejects_f32_8`). In the original script no `STORE` is typed
(`Whole.not_typedV_store10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config)
open Silmaril.Wasm.SpecTec.Sim (TypedV)

/-! ## Non-vacuity -/

variable (B : Builtins)

/-- The cases of the corrected `admininstr`. -/
noncomputable def adminCases10T : List TypCase :=
  (Sim.IntNumeric.recCases Silmaril.Wasm.SpecTec.Scripts.Wasm10.Original.d170 0 0).map fixCase10

set_option maxRecDepth 8000000 in
/-- The corrected `admininstr`, as `simEnv10T B` finds it. -/
theorem findTyp_admininstr10T : (simEnv10T B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT adminCases10T)]) := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
/-- Its `STORE` case is the corrected one. -/
theorem findCaseQ_adminStore10T : Sim.Typing.findCaseQ adminCases10T "STORE" =
    some (.tupT [.mk "valtype" (.varT "valtype" []), .mk "sz?" (.iterT (.varT "sz" []) .opt),
      .mk "memarg" (.varT "memarg" [])], [], [storePremFix10]) := by
  with_unfolding_all rfl

/-- **A payload the corrected case accepts is a typed `admininstr`.** -/
theorem typedV_adminStore10T {w : Value}
    (h : ∃ n, hasTypCase n (simEnv10T B) VarEnv.empty [storeCaseFix10] "STORE" w = .ok true) :
    TypedV (simEnv10T B) (.varT "admininstr" []) (.case "STORE" w) := by
  obtain ⟨ht, ρq, hb, hp⟩ := (hasTypCase_cons_hit_iffQ rfl).1 h
  have hc := Sim.Typing.hasTypCase_of_findCaseQ findCaseQ_adminStore10T ht hb hp
  exact Sim20.StoreFix.typedV_of_empty (hasTyp_varT_case rfl (findTyp_admininstr10T B)
    Equiv.evalArgs_nil matchArgs_nil hc)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `i32.store` is a typed `admininstr` in the corrected 1.0 script. -/
theorem typedV_i32Store10T : TypedV (simEnv10T B) (.varT "admininstr" [])
    (adminToV (.source (.intStore .i32 none ⟨0, 0⟩))) :=
  typedV_adminStore10T B ⟨60, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `i64.store8` is a typed `admininstr` in the corrected 1.0 script. -/
theorem typedV_i64Store8_10T : TypedV (simEnv10T B) (.varT "admininstr" [])
    (adminToV (.source (.intStore .i64 (some .i8) ⟨0, 0⟩))) :=
  typedV_adminStore10T B ⟨60, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `f32.store` is a typed `admininstr` in the corrected 1.0 script. -/
theorem typedV_f32Store10T : TypedV (simEnv10T B) (.varT "admininstr" [])
    (adminToV (.source (.floatStore .f32 ⟨0, 0⟩))) :=
  typedV_adminStore10T B ⟨60, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The premise is not vacuous**: the corrected case rejects a float store with a pack size
(at the primitives `Builtins.none`, by evaluation). -/
theorem storeCaseFix10_rejects_f32_8 :
    hasTypCase 60 (simEnv10T Builtins.none) VarEnv.empty [storeCaseFix10] "STORE"
      (.tuple [valTypeV (.float .f32), .opt (some (szV .i8)), memargV ⟨0, 0⟩]) = .ok false := by
  with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim10.StoreFix
