module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond2a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond2b
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond2bRelaxed

/-!
# Round 5: the second clause's condition definitely fails

`$halfop(…) = half` evaluates `$halfop` and then the unbound `half`: a definite failure, for every operator.
The per-family cases are in `Cond2a` and `Cond2b` (split to keep each module fast).
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

/-- **The second clause's leading condition definitely fails**, for every operator. -/
theorem evals_cond₂ (P : Profile) (hn : H → String) (host : HostSemantics H) (op : VecConvertOp)
    (l₁ m₁ l₂ m₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₂ l₁ m₁ l₂ m₂ (Vec.vConvertOpV op) w) cond₂ := by
  rcases op with ⟨h, sx⟩ | ⟨h, sx⟩ | ⟨sx, z⟩ | ⟨sx, z⟩ | _ | _
  · exact evals_cond₂_extend P hn host h sx l₁ m₁ l₂ m₂ w
  · exact evals_cond₂_convert P hn host h sx l₁ m₁ l₂ m₂ w
  · exact evals_cond₂_truncSat P hn host sx z l₁ m₁ l₂ m₂ w
  · exact evals_cond₂_relaxedTrunc P hn host sx z l₁ m₁ l₂ m₂ w
  all_goals exact Or.inr ⟨30, by cond_simp⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
