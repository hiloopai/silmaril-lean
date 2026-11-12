module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Basic

/-!
# Round 5: the second clause's condition definitely fails (`extend`, `convert`)

`$halfop(…) = half` evaluates `$halfop` and then the unbound `half`: a definite failure for `extend`
and `convert` (split from `Cond2` to keep each module fast).
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

/-- The leading condition definitely fails for `extend`. -/
theorem evals_cond₂_extend (P : Profile) (hn : H → String) (host : HostSemantics H)
    (h : Half) (sx : Signedness) (l₁ m₁ l₂ m₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₂ l₁ m₁ l₂ m₂ (Vec.vConvertOpV (.extend h sx)) w)
      cond₂ := by
  rcases h with _ | _ <;> rcases sx with _ | _ <;>
    exact Or.inr ⟨30, by cond_simp⟩

/-- The leading condition definitely fails for `convert`. -/
theorem evals_cond₂_convert (P : Profile) (hn : H → String) (host : HostSemantics H)
    (h : Option Half) (sx : Signedness) (l₁ m₁ l₂ m₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₂ l₁ m₁ l₂ m₂ (Vec.vConvertOpV (.convert h sx)) w)
      cond₂ := by
  rcases h with _ | _ | _ <;> rcases sx with _ | _ <;>
    exact Or.inr ⟨30, by cond_simp⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
