module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Basic

/-!
# Round 5: the first clause's condition evaluates (`trunc_sat`, signed)

`$halfop(…) = ε ∧ $zeroop(…) = ε` evaluates to a boolean for `trunc_sat`, at any shape values
(split from `Cond1b`, then from `Cond1bSat` by signedness, to keep each module fast).
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

/-- The first clause's leading condition evaluates for `trunc_sat`, signed. -/
theorem evals_cond₁_truncSat_signed (P : Profile) (hn : H → String) (host : HostSemantics H)
    (z : Bool) (l₁ m l₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host))
      (scope₁ l₁ m l₂ (Vec.vConvertOpV (.truncSat .signed z)) w) cond₁ := by
  rcases z with _ | _ <;> exact Or.inl ⟨_, 30, by cond_simp; rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
