module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond3a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond3b
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond3bRelaxed

/-!
# Round 5: the third clause's condition evaluates

`$zeroop(…) = ZERO` evaluates to a boolean for every operator, at any shape values.
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

/-- **The third clause's leading condition evaluates**, for every operator. -/
theorem evals_cond₃ (P : Profile) (hn : H → String) (host : HostSemantics H) (op : VecConvertOp)
    (l₁ m₁ l₂ m₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₂ l₁ m₁ l₂ m₂ (Vec.vConvertOpV op) w) cond₃ := by
  rcases op with ⟨h, sx⟩ | ⟨h, sx⟩ | ⟨sx, z⟩ | ⟨sx, z⟩ | _ | _
  · exact evals_cond₃_extend P hn host h sx l₁ m₁ l₂ m₂ w
  · exact evals_cond₃_convert P hn host h sx l₁ m₁ l₂ m₂ w
  · exact evals_cond₃_truncSat P hn host sx z l₁ m₁ l₂ m₂ w
  · exact evals_cond₃_relaxedTrunc P hn host sx z l₁ m₁ l₂ m₂ w
  all_goals exact Or.inl ⟨_, 30, by cond_simp; rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
