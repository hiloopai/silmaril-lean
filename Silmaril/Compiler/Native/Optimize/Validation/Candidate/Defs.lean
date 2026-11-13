module

public import Silmaril.Compiler.Native.Optimize.Validation.Observation.Thms
/-! Actual DAG-prefix and retained-leaf invariants for deriving pure candidate
success. The actual partial frame remains partial; no all-inputs-defined
premise or candidate-execution premise is introduced. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Candidate

structure Prefix (before after : Array Expr) : Prop where
  grows : before.size ≤ after.size
  old : ∀ index < before.size, after[index]? = before[index]?

def Growing {α : Type} (action : StateM State α) : Prop :=
  ∀ state, Prefix state.nodes (action.run state).2.nodes

/-- Every partial leaf in the actual retained DAG is old. -/
def Guarded (sourceSize : Nat) (nodes : Array Expr) : Prop :=
  ∀ index expression, nodes[index]? = some expression → expression.isPartialLeaf = true → index < sourceSize

end Silmaril.Compiler.Native.Optimize.Validation.Candidate
