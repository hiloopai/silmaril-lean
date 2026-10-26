module

public import Silmaril.Courses.Cambridge.L1.Exercises.DerivationPrinter

/-! # Cambridge L1 determinacy and Exercise 13

Theorem 1 is proved by induction on the first reduction derivation and
inversion of the second. The cases where a value would have to reduce close by
inverting that impossible premise. This covers the operator, sequence, while,
and conditional cases requested in Exercise 13.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

/-- Theorem 1: a configuration has at most one one-step successor. -/
theorem Step.deterministic {before firstResult secondResult : Config}
    (first : Step before firstResult) (second : Step before secondResult) :
    firstResult = secondResult := by
  induction first generalizing secondResult with
  | add =>
      cases second with
      | add => rfl
      | binaryLeft inner => cases inner
      | binaryRight _ inner => cases inner
  | ge =>
      cases second with
      | ge => rfl
      | binaryLeft inner => cases inner
      | binaryRight _ inner => cases inner
  | binaryLeft inner ih =>
      cases second with
      | add => cases inner
      | ge => cases inner
      | binaryLeft other =>
          have equal := ih other
          cases equal
          rfl
      | binaryRight value _ => exact False.elim (value_terminal value _ inner)
  | binaryRight value inner ih =>
      cases second with
      | add => cases inner
      | ge => cases inner
      | binaryLeft other => exact False.elim (value_terminal value _ other)
      | binaryRight _ other =>
          have equal := ih other
          cases equal
          rfl
  | deref firstPresent =>
      cases second with
      | deref secondPresent =>
          have equal : _ := firstPresent.symm.trans secondPresent
          cases Option.some.inj equal
          rfl
  | assignValue =>
      cases second with
      | assignValue => rfl
      | assignStep inner => cases inner
  | assignStep inner ih =>
      cases second with
      | assignValue => cases inner
      | assignStep other =>
          have equal := ih other
          cases equal
          rfl
  | seqSkip =>
      cases second with
      | seqSkip => rfl
      | seqStep inner => cases inner
  | seqStep inner ih =>
      cases second with
      | seqSkip => cases inner
      | seqStep other =>
          have equal := ih other
          cases equal
          rfl
  | ifTrue =>
      cases second with
      | ifTrue => rfl
      | ifStep inner => cases inner
  | ifFalse =>
      cases second with
      | ifFalse => rfl
      | ifStep inner => cases inner
  | ifStep inner ih =>
      cases second with
      | ifTrue => cases inner
      | ifFalse => cases inner
      | ifStep other =>
          have equal := ih other
          cases equal
          rfl
  | «while» =>
      cases second
      rfl

/-- Exercise 14's relation allows both operator-context rules at once. -/
def NondeterministicStep (before after : Config) : Prop :=
  Step before after ∨ Exercises.RightStep before after

theorem nondeterministic_operator_counterexample :
    NondeterministicStep Exercises.orderStart Exercises.leftAfter1 ∧
    NondeterministicStep Exercises.orderStart Exercises.rightAfter1 ∧
    Exercises.leftAfter1 ≠ Exercises.rightAfter1 := by
  constructor
  · exact Or.inl (Exercises.VariantStep.toOriginal Exercises.left_step1)
  constructor
  · exact Or.inr Exercises.right_step1
  · decide

theorem nondeterministic_not_determinate :
    ¬ ∀ before firstResult secondResult,
      NondeterministicStep before firstResult →
      NondeterministicStep before secondResult → firstResult = secondResult := by
  intro deterministic
  exact nondeterministic_operator_counterexample.2.2
    (deterministic _ _ _ nondeterministic_operator_counterexample.1
      nondeterministic_operator_counterexample.2.1)

end Silmaril.Courses.Cambridge.L1
