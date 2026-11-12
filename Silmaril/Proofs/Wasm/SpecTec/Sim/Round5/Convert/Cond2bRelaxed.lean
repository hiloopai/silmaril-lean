module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Basic

/-!
# Round 5: the second clause's condition definitely fails (`relaxed_trunc`)

`$halfop(…) = half` evaluates `$halfop` and then the unbound `half`: a definite failure for
`trunc_sat` and `relaxed_trunc` (split from `Cond2` to keep each module fast).

The `relaxed_trunc` case, split from `Cond2b` to keep each module fast.
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

/-- The leading condition definitely fails for `relaxed_trunc`. -/
theorem evals_cond₂_relaxedTrunc (P : Profile) (hn : H → String) (host : HostSemantics H)
    (sx : Signedness) (z : Bool) (l₁ m₁ l₂ m₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₂ l₁ m₁ l₂ m₂ (Vec.vConvertOpV (.relaxedTrunc sx z))
      w) cond₂ := by
  rcases sx with _ | _ <;> rcases z with _ | _ <;>
    exact Or.inr ⟨30, by cond_simp⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
