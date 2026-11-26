module

public import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Completion
public import Silmaril.Languages.Python.Core.Closure.Call.Thms
import Silmaril.Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults.Correctness

public section

namespace Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults

variable {layout : Layout} {parameters : Parameters layout} {defaults : PositionalDefaults parameters}
  {supplied arguments : List Value} {before after : Environment layout}

theorem bind_full (arity : supplied.length = parameters.slots.length) :
    defaults.bind supplied before = bindPositional parameters supplied before := by
  simp [bind, complete_full arity, Except.bind]

theorem bind_iff :
    defaults.bind supplied before = .ok after ↔
      ∃ arguments, defaults.complete supplied = .ok arguments ∧
        Writes (parameters.slots.zip arguments) before after :=
  Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults.bind_iff

theorem bind_read (completed : defaults.complete supplied = .ok arguments)
    (bound : defaults.bind supplied before = .ok after) (unique : Function.Injective before.2.owned)
    {slot : ParameterSlot layout} {value : Value} (member : (slot, value) ∈ parameters.slots.zip arguments) :
    after.2.read after.1 slot.slot = .ok value :=
  Call.bind_read (by simpa only [bind, completed, Except.bind] using bound) unique member

theorem bind_too_few (missing : supplied.length < defaults.required) :
    defaults.bind supplied before = .error (.defined (.positionalArity defaults.required supplied.length)) := by
  simp [bind, complete, missing, Except.bind]

theorem bind_too_many (extra : parameters.slots.length < supplied.length) :
    defaults.bind supplied before = .error (.defined (.positionalArity parameters.slots.length supplied.length)) := by
  have enough : ¬ supplied.length < defaults.required := Nat.not_lt.mpr ((Nat.sub_le _ _).trans extra.le)
  simp [bind, complete, enough, extra, Except.bind]

end Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults
