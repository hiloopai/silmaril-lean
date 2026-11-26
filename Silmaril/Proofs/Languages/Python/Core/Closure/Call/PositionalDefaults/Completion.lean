module

public import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Defs

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout} {parameters : Parameters layout} {defaults : PositionalDefaults parameters}
  {supplied arguments : List Value}

theorem complete_iff :
    defaults.complete supplied = .ok arguments ↔
      defaults.required ≤ supplied.length ∧ supplied.length ≤ parameters.slots.length ∧
        arguments = supplied ++ defaults.values.drop (supplied.length - defaults.required) := by
  by_cases missing : supplied.length < defaults.required
  · simp [PositionalDefaults.complete, missing, Nat.not_le.mpr missing]
  · by_cases extra : parameters.slots.length < supplied.length
    · simp [PositionalDefaults.complete, missing, extra, Nat.not_le.mpr extra]
    · simp [PositionalDefaults.complete, missing, extra, Nat.le_of_not_lt missing, Nat.le_of_not_lt extra,
        eq_comm]

theorem complete_length (completed : defaults.complete supplied = .ok arguments) :
    arguments.length = parameters.slots.length := by
  obtain ⟨enough, within, rfl⟩ := complete_iff.mp completed
  rw [List.length_append, List.length_drop]
  have fits := defaults.fits
  unfold PositionalDefaults.required at *
  omega

theorem complete_full (arity : supplied.length = parameters.slots.length) :
    defaults.complete supplied = .ok supplied := by
  have within : defaults.required ≤ supplied.length := by
    rw [arity]
    exact Nat.sub_le _ _
  apply complete_iff.mpr
  refine ⟨within, arity.le, ?_⟩
  have fits := defaults.fits
  have used : defaults.values.length ≤ supplied.length - defaults.required := by
    unfold PositionalDefaults.required
    omega
  rw [List.drop_eq_nil_of_le used, List.append_nil]

theorem completeArguments_length {saved : List Silmaril.Languages.Python.Core.Module.Value}
    (success : completeArguments parameters saved supplied = .ok arguments) :
    arguments.length = parameters.slots.length := by
  unfold completeArguments at success
  split at success
  · exact complete_length success
  · contradiction

theorem completeArguments_empty :
    completeArguments parameters [] supplied = .ok arguments ↔
      supplied.length = parameters.slots.length ∧ supplied = arguments := by
  simp only [completeArguments, List.length_nil, Nat.zero_le, dite_true, complete_iff,
    PositionalDefaults.required, List.map_nil, Nat.sub_zero, List.drop_nil, List.append_nil]
  constructor
  · rintro ⟨enough, within, rfl⟩
    exact ⟨Nat.le_antisymm within enough, rfl⟩
  · rintro ⟨arity, rfl⟩
    exact ⟨arity.ge, arity.le, rfl⟩

end Silmaril.Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults
