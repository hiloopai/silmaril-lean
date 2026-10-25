module

public import Silmaril.Wasm.Execution.Core.Store

@[expose] public section

/-! # Reduction family: parametric instructions (pure)

Spec rules (all present): `Step_pure/unreachable`, `Step_pure/nop`,
`Step_pure/drop`, `Step_pure/select-true`, `Step_pure/select-false`.
-/

namespace Silmaril.Wasm.Execution.Core

inductive ParametricStep : List Admin → List Admin → Prop where
  /-- `Step_pure/unreachable`. -/
  | unreachable : ParametricStep [.plain .unreachable] [.trap]
  /-- `Step_pure/nop`. -/
  | nop : ParametricStep [.plain .nop] []
  /-- `Step_pure/drop`. -/
  | drop (v : Val) : ParametricStep [v.toAdmin, .plain .drop] []
  /-- `Step_pure/select-true`. -/
  | selectTrue {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List ValType)} (hc : c ≠ 0) :
      ParametricStep [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)] [v₁.toAdmin]
  /-- `Step_pure/select-false`. -/
  | selectFalse (v₁ v₂ : Val) (ts : Option (List ValType)) :
      ParametricStep [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)] [v₂.toAdmin]

end Silmaril.Wasm.Execution.Core
