module

public import Silmaril.Numeric.Ieee754.Environment

/-!
# Exception environment regressions

These examples check masked restoration, snapshots, any-selected-flag queries,
and sticky sequencing. The supplied `Result.flags` are test data; these tests
make no claim about which numerical operation produces those flags.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.EnvironmentTests

/-- A program without inherited status starts with no flags raised. -/
theorem initially_clear : Environment.initial.testFlags Flags.all = false := by decide

/-- A combined query means "any", even when another selected flag is clear. -/
theorem query_any_selected :
    (Environment.initial.raiseFlags (Flags.singleton .inexact)).testFlags
      ((Flags.singleton .underflow).union (Flags.singleton .inexact)) = true := by decide

/-- Unselected raised flags do not satisfy a query. -/
theorem query_ignores_unselected :
    (Environment.initial.raiseFlags (Flags.singleton .inexact)).testFlags
      (Flags.singleton .overflow) = false := by decide

/-- Raising one class does not imply another; numerical handlers must supply both
flags when the standard requires them (e.g. default overflow and inexact). -/
theorem raise_is_explicit :
    (Environment.initial.raiseFlags (Flags.singleton .overflow)).flags =
      (Flags.singleton .overflow) := by decide

/-- Clearing one flag leaves a different raised flag intact. -/
theorem lower_preserves_unselected :
    ((Environment.initial.raiseFlags
      ((Flags.singleton .overflow).union (Flags.singleton .inexact))).lowerFlags
        (Flags.singleton .overflow)).flags = Flags.singleton .inexact := by decide

/-- A saved snapshot is independent of subsequent changes to the environment. -/
theorem saved_snapshot_unchanged :
    let original := Environment.initial.raiseFlags (Flags.singleton .inexact)
    let saved := original.saveAllFlags
    let changed := original.lowerFlags Flags.all
    Environment.testSavedFlags saved (Flags.singleton .inexact) = true ∧
      changed.testFlags (Flags.singleton .inexact) = false := by decide

/-- Masked restoration can clear a selected flag without clearing unselected ones. -/
theorem restore_selected_false :
    ((Environment.initial.raiseFlags
      ((Flags.singleton .invalidOperation).union (Flags.singleton .divisionByZero))).restoreFlags
        Flags.empty (Flags.singleton .invalidOperation)).flags =
      Flags.singleton .divisionByZero := by decide

/-- Restoring an unselected saved flag must not raise it. -/
theorem restore_does_not_import_unselected :
    (Environment.initial.restoreFlags (Flags.singleton .overflow) (Flags.singleton .inexact)).flags =
      Flags.empty := by decide

/-- Multiple operations accumulate their flags while keeping the latest return value. -/
theorem sequential_commit :
    let first : Result Nat := ⟨4, Flags.singleton .inexact⟩
    let second : Nat → Result Nat := fun n => ⟨n + 3, Flags.singleton .divisionByZero⟩
    Environment.initial.commit (first.bind second) =
      (7, { Environment.initial with
        flags := (Flags.singleton .inexact).union (Flags.singleton .divisionByZero) }) := by decide

/-- Repeated raises are sticky and idempotent, not counted occurrences. -/
theorem repeated_commit_idempotent :
    let result : Result Unit := ⟨(), Flags.singleton .inexact⟩
    let once := (Environment.initial.commit result).2
    (once.commit result).2 = once := by decide

/-- Neither commits nor explicit status restoration modify arithmetic attributes. -/
theorem attributes_preserved :
    let env : Environment := { rounding := .towardNegative, tininess := .beforeRounding }
    let result : Result F32 := ⟨⟨0x80000000⟩, Flags.singleton .underflow⟩
    let committed := env.commit result
    committed.1.bits = 0x80000000 ∧ committed.2.rounding = .towardNegative ∧
      committed.2.tininess = .beforeRounding ∧
      (committed.2.restoreFlags Flags.empty Flags.all).rounding = .towardNegative := by decide

/-- A pure result leaves inherited flags intact. -/
theorem pure_keeps_inherited :
    let env := Environment.initial.raiseFlags (Flags.singleton .invalidOperation)
    env.commit (Result.pure 12) = (12, env) := by decide

end Silmaril.Numeric.Ieee754.EnvironmentTests
