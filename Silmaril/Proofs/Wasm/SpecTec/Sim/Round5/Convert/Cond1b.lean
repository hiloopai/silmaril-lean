module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond1bSat
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond1bRel

/-!
# Round 5: the first clause's condition evaluates (truncations, `demote`, `promote`)

`$halfop(…) = ε ∧ $zeroop(…) = ε` evaluates to a boolean for every operator, at any shape values.
The truncations are evaluated in `Cond1bSat` and `Cond1bRel` (split to keep each module fast).
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

/-- The first clause's leading condition evaluates for the truncations, `demote` and
`promote`. -/
theorem evals_cond₁_trunc (P : Profile) (hn : H → String) (host : HostSemantics H)
    (op : VecConvertOp) (hop : ∀ h sx, op ≠ .extend h sx) (hop' : ∀ h sx, op ≠ .convert h sx)
    (l₁ m l₂ w : Value) :
    EvalsOrUndef (simEnv (BI P hn host)) (scope₁ l₁ m l₂ (Vec.vConvertOpV op) w) cond₁ := by
  rcases op with ⟨h, sx⟩ | ⟨h, sx⟩ | ⟨sx, z⟩ | ⟨sx, z⟩ | _ | _
  · exact absurd rfl (hop h sx)
  · exact absurd rfl (hop' h sx)
  · exact evals_cond₁_truncSat P hn host sx z l₁ m l₂ w
  · exact evals_cond₁_relaxedTrunc P hn host sx z l₁ m l₂ w
  all_goals exact Or.inl ⟨_, 30, by cond_simp; rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
