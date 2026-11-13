module

public import Silmaril.Cerberus.Assertion.Pure.Defs

/-! Kernel-checked examples and counterexamples for the supported assertion subset.
These operate on mathematical integers; no C overflow claim is made. -/

@[expose] public section
namespace Silmaril.Cerberus.Assertion.Pure.Checks

def zeroEnv : Env := fun _ => 0

/-- A typical normalized ACSL/CN postcondition for an increment operation. -/
def incrementPost : Formula :=
  .eq (.var "result") (.add (.var "old_x") (.literal 1))

theorem increment_goal (x : Int) :
    incrementPost.leanGoal (fun name => if name = "result" then x + 1 else x) := by
  apply (Formula.leanGoal_correct _ _).mpr
  simp [incrementPost, Formula.holds, Term.eval]

/-- A rejected assertion is checked as well as successful examples. -/
theorem wrong_increment_rejected :
    incrementPost.check (fun name => if name = "result" then 8 else 6) = false := by
  decide +kernel

/-- Unsigned-C-style wraparound is intentionally not mathematical addition. -/
theorem wrapping_is_not_integer_increment :
    incrementPost.check (fun name => if name = "result" then 0 else 255) = false := by
  decide +kernel

def increasing : RichFormula :=
  .all "x" (.pure (.lt (.var "x") (.add (.var "x") (.literal 1))))

theorem increasing_goal : increasing.leanGoal zeroEnv := by
  apply (RichFormula.leanGoal_correct _ _).mpr
  intro n
  simp [RichFormula.holds, Formula.holds, Term.eval, bind]
  omega

/-- The existential layer preserves witnesses, including negative integers. -/
def negativeWitness : RichFormula :=
  .ex "x" (.pure (.eq (.add (.var "x") (.literal 3)) (.literal 0)))

theorem negativeWitness_goal : negativeWitness.leanGoal zeroEnv := by
  apply (RichFormula.leanGoal_correct _ _).mpr
  exact ⟨-3, by simp [RichFormula.holds, Formula.holds, Term.eval, bind]⟩

/-- An inner binder shadows the outer value, rather than constraining it. -/
def shadowing : RichFormula :=
  .all "x" (.ex "x" (.pure (.eq (.var "x") (.literal 7))))

theorem shadowing_goal : shadowing.leanGoal zeroEnv := by
  apply (RichFormula.leanGoal_correct _ _).mpr
  intro n
  exact ⟨7, by simp [RichFormula.holds, Formula.holds, Term.eval, bind]⟩

end Silmaril.Cerberus.Assertion.Pure.Checks
