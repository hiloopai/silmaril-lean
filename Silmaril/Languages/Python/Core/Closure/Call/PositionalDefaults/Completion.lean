module

public import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults.Completion

public section

namespace Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults

variable {layout : Layout} {parameters : Parameters layout} {defaults : PositionalDefaults parameters}
  {supplied arguments : List Value}

theorem complete_iff :
    defaults.complete supplied = .ok arguments ↔
      defaults.required ≤ supplied.length ∧ supplied.length ≤ parameters.slots.length ∧
        arguments = supplied ++ defaults.values.drop (supplied.length - defaults.required) :=
  Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults.complete_iff

theorem complete_length (completed : defaults.complete supplied = .ok arguments) :
    arguments.length = parameters.slots.length :=
  Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults.complete_length completed

theorem complete_prefix (completed : defaults.complete supplied = .ok arguments) :
    arguments.take supplied.length = supplied := by
  rw [(complete_iff.mp completed).2.2]
  simp

theorem complete_full (arity : supplied.length = parameters.slots.length) :
    defaults.complete supplied = .ok supplied :=
  Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults.complete_full arity

end Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults

namespace Silmaril.Languages.Python.Core.Closure.Call

theorem completeArguments_length {layout : Layout} {parameters : Parameters layout}
    {saved : List Core.Module.Value} {supplied completed : List Value}
    (success : completeArguments parameters saved supplied = .ok completed) :
    completed.length = parameters.slots.length :=
  Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults.completeArguments_length success

@[simp] theorem completeArguments_empty {layout : Layout} {parameters : Parameters layout}
    {supplied completed : List Value} :
    completeArguments parameters [] supplied = .ok completed ↔
      supplied.length = parameters.slots.length ∧ supplied = completed :=
  Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults.completeArguments_empty

end Silmaril.Languages.Python.Core.Closure.Call
