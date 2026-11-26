module

public import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Completion
public import Silmaril.Languages.Python.Core.Closure.Call.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout} {parameters : Parameters layout} {defaults : PositionalDefaults parameters}
  {supplied arguments : List Value} {before after : Environment layout}

theorem bind_iff :
    defaults.bind supplied before = .ok after ↔
      ∃ arguments, defaults.complete supplied = .ok arguments ∧
        Writes (parameters.slots.zip arguments) before after := by
  cases completed : defaults.complete supplied with
  | error failure => simp [PositionalDefaults.bind, completed, Except.bind]
  | ok exactArgs =>
    constructor
    · intro bound
      have result : bindPositional parameters exactArgs before = .ok after := by
        simpa only [PositionalDefaults.bind, completed, Except.bind] using bound
      exact ⟨exactArgs, rfl, (Call.bind_iff.mp result).2⟩
    · rintro ⟨_, same, writes⟩
      cases same
      have result := Call.bind_iff.mpr ⟨Call.PositionalDefaults.complete_length completed, writes⟩
      simpa only [PositionalDefaults.bind, completed, Except.bind] using result

end Silmaril.Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults
