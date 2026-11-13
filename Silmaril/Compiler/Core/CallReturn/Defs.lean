module

public import Silmaril.Compiler.Core.CalleeReturn.Defs
public import Silmaril.Compiler.Core.Verified.Call.Defs

/-! A proof contract for actual locally forced pure Core evaluation, used by
zero-argument call composition. It supplies no alternate evaluator or result. -/
@[expose] public section
namespace Silmaril.Compiler.Core.CallReturn
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core
variable {file : Program} {labels : Labels}

/-- A proof-device contract on actual locally forced pure transitions. -/
def PureForced (expression : PE) (environment : Env) (value : Val) : Prop :=
  ∀ frames memory, Forced.Reaches file labels
    ⟨.pureExpr expression environment, frames, memory⟩ ⟨.value value, frames, memory⟩

end Silmaril.Compiler.Core.CallReturn
