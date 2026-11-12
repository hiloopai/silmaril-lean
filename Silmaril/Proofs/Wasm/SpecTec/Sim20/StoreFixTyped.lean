module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFix
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixNeed

/-!
# The `STORE` erratum types what the original refutes

Non-vacuity of `StoreFix.simEnv20T`, by evaluation of `hasTyp` at every builtins:
* `typedV_i32Store20T`, `typedV_i64Store8_20T`, `typedV_f32Store20T`: `i32.store`,
  `i64.store8` and `f32.store` (at `memarg` `0 0`) are typed `admininstr`s. In the original
  script none is (`Whole.not_typedV_store20`);
* `storeCaseFix_rejects_f32_8`: the premise is not vacuous: a float store with a pack size is
  still rejected;
* `typed20T_storeFnCfg`: the configuration `storeFnCfg` (a store holding a function
  whose body is `i32.store`, code `nop`) has a typed image. In `simEnv20S` its state is
  untyped and the script is stuck there (`stuck_storeFn20S`).

The forward rules are not transferred to `simEnv20T` here: every forward lemma of the 2.0 route
is stated in `simEnv20`/`simEnv20S`, and moving them needs an agreement theorem for `hasTyp`
between the two type tables (they differ only in the `STORE` case; evaluation reads types only
through `subCaseOk`, which sees case names). That theorem is open.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.Whole (not_typedV_store20)

/-! ## Non-vacuity -/

variable (B : Builtins)

/-- A closed type name, from the empty scope. -/
theorem typedV_of_empty {env : Env} {x : IL.Id} {v : Value}
  (h : HasTyp env VarEnv.empty (.varT x []) v) : TypedV env (.varT x []) v :=
  fun _ hρ => Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ h

/-- The cases of the corrected `admininstr`. -/
noncomputable def adminCasesT : List TypCase :=
  (Sim.IntNumeric.recCases Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d295 0 0).map fixCase

set_option maxRecDepth 8000000 in
/-- The corrected `admininstr`, as `simEnv20T B` finds it. -/
theorem findTyp_admininstr20T : (simEnv20T B).findTyp? "admininstr" =
  some ([], [.instD [] [] (.variantT adminCasesT)]) := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
/-- Its `STORE` case is the corrected one. -/
theorem findCaseQ_adminStoreT : Sim.Typing.findCaseQ adminCasesT "STORE" =
  some (.tupT [.mk "numtype" (.varT "numtype" []), .mk "sz?" (.iterT (.varT "sz" []) .opt),
      .mk "memarg" (.varT "memarg" [])], [], [storePremFix]) := by
  with_unfolding_all rfl

/-- **A payload the corrected case accepts is a typed `admininstr`.** -/
theorem typedV_adminStoreT {w : Value}
  (h : ∃ n, hasTypCase n (simEnv20T B) VarEnv.empty [storeCaseFix] "STORE" w = .ok true) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (.case "STORE" w) := by
  obtain ⟨ht, ρq, hb, hp⟩ := (hasTypCase_cons_hit_iffQ rfl).1 h
  have hc := Sim.Typing.hasTypCase_of_findCaseQ findCaseQ_adminStoreT ht hb hp
  exact typedV_of_empty (hasTyp_varT_case rfl (findTyp_admininstr20T B) Equiv.evalArgs_nil
  matchArgs_nil hc)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `i32.store` is a typed `admininstr` in the corrected script. -/
theorem typedV_i32Store20T : TypedV (simEnv20T B) (.varT "admininstr" [])
  (adminToV (.plain (.intStore .i32 none ⟨0, 0⟩))) :=
  typedV_adminStoreT B ⟨60, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `i64.store8` is a typed `admininstr` in the corrected script. -/
theorem typedV_i64Store8_20T : TypedV (simEnv20T B) (.varT "admininstr" [])
  (adminToV (.plain (.intStore .i64 (some .i8) ⟨0, 0⟩))) :=
  typedV_adminStoreT B ⟨60, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `f32.store` is a typed `admininstr` in the corrected script. -/
theorem typedV_f32Store20T : TypedV (simEnv20T B) (.varT "admininstr" [])
  (adminToV (.plain (.floatStore .f32 ⟨0, 0⟩))) :=
  typedV_adminStoreT B ⟨60, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The premise is not vacuous**: the corrected case rejects a float store with a pack size
(at the primitives `Builtins.none`, by evaluation). -/
theorem storeCaseFix_rejects_f32_8 :
  hasTypCase 60 (simEnv20T Builtins.none) VarEnv.empty [storeCaseFix] "STORE"
      (.tuple [numTypeV (.float .f32), .opt (some (szV .i8)), memargV ⟨0, 0⟩]) = .ok false := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The storing configuration is typed in the corrected script.** In `simEnv20S` its state
has no type and no step (`stuck_storeFn20S`). -/
theorem typed20T_storeFnCfg {H : Type} (hn : H → String) :
    Typed20 (simEnv20T B) hn storeFnCfg :=
  ⟨300, by with_unfolding_all rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.StoreFix
