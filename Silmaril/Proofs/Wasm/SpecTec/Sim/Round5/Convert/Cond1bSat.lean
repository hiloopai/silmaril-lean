module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond1bSatS
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond1bSatU

/-!
# Round 5: the first clause's condition evaluates (`trunc_sat`)

`$halfop(…) = ε ∧ $zeroop(…) = ε` evaluates to a boolean for `trunc_sat`, at any shape values
(split from `Cond1b` to keep each module fast; the two signednesses are in `Cond1bSatS` and
`Cond1bSatU`).
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

/-- The first clause's leading condition evaluates for `trunc_sat`. -/
theorem evals_cond₁_truncSat (P : Profile) (hn : H → String) (host : HostSemantics H)
    (sx : Signedness) (z : Bool) (l₁ m l₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₁ l₁ m l₂ (Vec.vConvertOpV (.truncSat sx z)) w)
      cond₁ := by
  rcases sx with _ | _ <;>
    first
      | exact evals_cond₁_truncSat_signed P hn host z l₁ m l₂ w
      | exact evals_cond₁_truncSat_unsigned P hn host z l₁ m l₂ w

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
