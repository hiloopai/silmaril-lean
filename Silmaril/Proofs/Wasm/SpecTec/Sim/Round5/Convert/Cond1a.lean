module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Basic

/-!
# Round 5: the first clause's condition evaluates (`extend`, `convert`)

`$halfop(…) = ε ∧ $zeroop(…) = ε` evaluates to a boolean for every operator, at any shape values.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Convert

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30
open Round4Int (BI)
open Simd (clausesOf findDef_Halfop findDef_Zeroop)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type}

/-- The first clause's leading condition evaluates for `extend`. -/
theorem evals_cond₁_extend (P : Profile) (hn : H → String) (host : HostSemantics H) (h : Half)
    (sx : Signedness) (l₁ m l₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₁ l₁ m l₂ (Vec.vConvertOpV (.extend h sx)) w)
      cond₁ := by
  rcases h with _ | _ <;> rcases sx with _ | _ <;> exact Or.inl ⟨_, 30, by cond_simp; rfl⟩

/-- The first clause's leading condition evaluates for `convert`. -/
theorem evals_cond₁_convert (P : Profile) (hn : H → String) (host : HostSemantics H)
    (h : Option Half) (sx : Signedness) (l₁ m l₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₁ l₁ m l₂ (Vec.vConvertOpV (.convert h sx)) w)
      cond₁ := by
  rcases h with _ | _ | _ <;> rcases sx with _ | _ <;> exact Or.inl ⟨_, 30, by cond_simp; rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
