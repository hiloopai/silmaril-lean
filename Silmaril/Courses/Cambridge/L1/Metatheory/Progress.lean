module

public import Silmaril.Courses.Cambridge.L1.Metatheory.Inversion

/-! # Cambridge L1 progress and Exercise 15

The store covers the typing environment when every typed location is already
allocated. Canonical-form lemmas identify typed values so that the primitive
operator, conditional, assignment, and sequence rules can fire.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

def StoreCovers (Γ : TypeEnv) (s : Store) : Prop :=
  ∀ loc, loc ∈ Γ → loc ∈ s

theorem typed_integer_value {Γ : TypeEnv} {e : Expr}
    (typing : HasType Γ e .int) (value : IsValue e) : ∃ n, e = .int n := by
  cases value with
  | int n => exact ⟨n, rfl⟩
  | bool => cases typing
  | skip => cases typing

theorem typed_boolean_value {Γ : TypeEnv} {e : Expr}
    (typing : HasType Γ e .bool) (value : IsValue e) : ∃ b, e = .bool b := by
  cases value with
  | int => cases typing
  | bool b => exact ⟨b, rfl⟩
  | skip => cases typing

theorem typed_unit_value {Γ : TypeEnv} {e : Expr}
    (typing : HasType Γ e .unit) (value : IsValue e) : e = .skip := by
  cases value with
  | int => cases typing
  | bool => cases typing
  | skip => rfl

/-- Theorem 2: well-typed expressions are values or can take a step. -/
theorem progress {Γ : TypeEnv} {e : Expr} {T : Ty} {s : Store}
    (typing : HasType Γ e T) (covers : StoreCovers Γ s) :
    IsValue e ∨ ∃ after, Step ⟨e, s⟩ after := by
  induction typing generalizing s with
  | int n => exact Or.inl (.int n)
  | bool b => exact Or.inl (.bool b)
  | add hl hr ihLeft ihRight =>
      rcases ihLeft covers with valueLeft | ⟨next, stepLeft⟩
      · rcases ihRight covers with valueRight | ⟨next, stepRight⟩
        · obtain ⟨a, rfl⟩ := typed_integer_value hl valueLeft
          obtain ⟨b, rfl⟩ := typed_integer_value hr valueRight
          exact Or.inr ⟨⟨.int (a + b), s⟩, .add a b s⟩
        · exact Or.inr ⟨⟨.binary _ .add next.expr, next.store⟩,
            .binaryRight valueLeft stepRight⟩
      · exact Or.inr ⟨⟨.binary next.expr .add _, next.store⟩,
          .binaryLeft stepLeft⟩
  | ge hl hr ihLeft ihRight =>
      rcases ihLeft covers with valueLeft | ⟨next, stepLeft⟩
      · rcases ihRight covers with valueRight | ⟨next, stepRight⟩
        · obtain ⟨a, rfl⟩ := typed_integer_value hl valueLeft
          obtain ⟨b, rfl⟩ := typed_integer_value hr valueRight
          exact Or.inr ⟨⟨.bool (a ≥ b), s⟩, .ge a b s⟩
        · exact Or.inr ⟨⟨.binary _ .ge next.expr, next.store⟩,
            .binaryRight valueLeft stepRight⟩
      · exact Or.inr ⟨⟨.binary next.expr .ge _, next.store⟩,
          .binaryLeft stepLeft⟩
  | cond hc hy hn ihTest _ _ =>
      rcases ihTest covers with valueTest | ⟨next, stepTest⟩
      · obtain ⟨b, rfl⟩ := typed_boolean_value hc valueTest
        cases b
        · exact Or.inr ⟨⟨_, s⟩, .ifFalse⟩
        · exact Or.inr ⟨⟨_, s⟩, .ifTrue⟩
      · exact Or.inr ⟨⟨.cond next.expr _ _, next.store⟩, .ifStep stepTest⟩
  | assign present he ih =>
      rcases ih covers with value | ⟨next, step⟩
      · obtain ⟨n, rfl⟩ := typed_integer_value he value
        exact Or.inr ⟨⟨.skip, s.insert _ n⟩,
          .assignValue (covers _ present)⟩
      · exact Or.inr ⟨⟨.assign _ next.expr, next.store⟩, .assignStep step⟩
  | deref present =>
      obtain ⟨n, found⟩ := Finmap.mem_iff.mp (covers _ present)
      exact Or.inr ⟨⟨.int n, s⟩, .deref found⟩
  | skip => exact Or.inl .skip
  | seq hl hr ihLeft _ =>
      rcases ihLeft covers with valueLeft | ⟨next, stepLeft⟩
      · have skip := typed_unit_value hl valueLeft
        subst_vars
        exact Or.inr ⟨⟨_, s⟩, .seqSkip⟩
      · exact Or.inr ⟨⟨.seq next.expr _, next.store⟩, .seqStep stepLeft⟩
  | loop _ _ _ _ =>
      exact Or.inr ⟨⟨_, s⟩, .while⟩

/-- A well-typed configuration with a covering store cannot be stuck. -/
theorem not_stuck {Γ : TypeEnv} {e : Expr} {T : Ty} {s : Store}
    (typing : HasType Γ e T) (covers : StoreCovers Γ s) :
    ¬ Stuck ⟨e, s⟩ := by
  intro ⟨notValue, terminal⟩
  rcases progress typing covers with value | ⟨next, step⟩
  · exact notValue value
  · exact terminal next step

end Silmaril.Courses.Cambridge.L1
