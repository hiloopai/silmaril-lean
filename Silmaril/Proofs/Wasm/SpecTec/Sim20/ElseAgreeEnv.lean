module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.ElseAgree.Typ

/-!
# `simEnv20S` and `simEnv20T` type alike off `tbad20`

* `typsOffB_fixedS20` (kernel): every type of the corrected wasm-2.0 script outside `tbad20`
  unfolds to types outside `tbad20`. So `tbad20` is the set of types that reach `instr` or
  `admininstr`.
* `typOff20T`: the type tables of `simEnv20S B` and `simEnv20T B` agree outside `tbad20`.
* **`hasTyp_off20T`**: so at a type off `tbad20`, in a scope without type variables, a value is
  typed in `simEnv20T B` exactly when it is in `simEnv20S B`.
* `hasTyp_varT_scope`: a named type without arguments types a value alike in any two scopes
  without type variables. The type is unfolded in the scope of its instance, which is empty.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.ElseAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp evInst mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (envSame20T simEnv20T_tables find?_map_repl)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Every type of the corrected wasm-2.0 script outside `tbad20` unfolds to types outside
`tbad20`** (kernel). -/
theorem typsOffB_fixedS20 : typsOffB tbad20 (typsOfDefs StepFix.fixedS20) = true := by
  decide +kernel

/-- **The type tables of `simEnv20S B` and `simEnv20T B` agree off `tbad20`.** -/
theorem typOff20T (B : Builtins) : TypOff tbad20 (simEnv20S B) (simEnv20T B) := by
  refine ⟨fun x hx => ?_, fun x td hx hd => ?_⟩
  · have ha : x ≠ "admininstr" := by rintro rfl; simp [tbad20] at hx
    have hi : x ≠ "instr" := by rintro rfl; simp [tbad20] at hx
    have ht := (simEnv20T_tables B).1
    simp only [Env.findTyp?, ht, find?_map_repl]
    simp [ha, hi]
  · have hm : (x, td) ∈ typsOfDefs StepFix.fixedS20 := by
      have h' : (typsOfDefs StepFix.fixedS20).find? x = some td := by
        simpa [simEnv20S, Env.withBuiltins, Env.findTyp?, envOfScript, envOfDefs_eq, Env.empty,
          Map.empty] using hd
      exact mem_of_find? h'
    have h := List.all_eq_true.1 typsOffB_fixedS20 _ hm
    simp only [hx, Bool.false_or] at h
    intro i hi
    exact goodT_of_all (List.all_eq_true.1 h i hi)

/-- A scope without type variables. -/
theorem typsOkT_nil {ρ : VarEnv} (h : ρ.typs = []) : TypsOkT tbad20 ρ := by
  intro p hp; rw [h] at hp; cases hp

/-- **Off `tbad20`, `simEnv20T B` types as `simEnv20S B`.** -/
theorem hasTyp_off20T (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {t : Typ} {v : Value}
    (ht : GoodT tbad20 (evTyp t)) : HasTyp (simEnv20T B) ρ t v ↔ HasTyp (simEnv20S B) ρ t v :=
  hasTyp_off_iff (envSame20T B) (typOff20T B) (typsOkT_nil hρ) ht

/-- At a named type without arguments, `hasTyp` does not read the values of the scope. -/
theorem hasTyp_varT_eq {env : Env} {ρ ρ' : VarEnv} (hρ : ρ.typs = []) (hρ' : ρ'.typs = [])
    (n : Nat) (x : IL.Id) (v : Value) :
    hasTyp n env ρ (.varT x []) v = hasTyp n env ρ' (.varT x []) v := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ]
  have hl' : localTyp? ρ' x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ']
  rcases n with _ | _ | n
  · simp only [hasTyp]
  · simp only [hasTyp, hl, hl']
    simp [evalArgs]
  · simp only [hasTyp, hl, hl']
    simp [evalArgs]

/-- **A named type without arguments types alike in two scopes without type variables.** -/
theorem hasTyp_varT_scope {env : Env} {ρ ρ' : VarEnv} (hρ : ρ.typs = []) (hρ' : ρ'.typs = [])
    {x : IL.Id} {v : Value} (h : HasTyp env ρ (.varT x []) v) : HasTyp env ρ' (.varT x []) v :=
  let ⟨n, hn⟩ := h
  ⟨n, (hasTyp_varT_eq hρ' hρ n x v).trans hn⟩

end Silmaril.Wasm.SpecTec.Sim20.ElseAgree
