module

public import Silmaril.Courses.Cambridge.L1.Metatheory.Preservation

/-! # Cambridge L1 Exercise 17: preservation by typing induction

This is a second proof of the expression-type clause of Theorem 3. It follows
the typing derivation, then inverts the reduction in each typing-rule case.
It does not use `Step.preserves_type`; only the store-domain lemma is reused to
obtain the coverage clause of the full theorem.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

theorem preserves_type_by_typing {Γ : TypeEnv} {e : Expr} {T : Ty}
    (typing : HasType Γ e T) :
    ∀ (s : Store) (after : Config), Step ⟨e, s⟩ after → HasType Γ after.expr T := by
  induction typing with
  | int =>
      intro s after step
      cases step
  | bool =>
      intro s after step
      cases step
  | add hl hr ihLeft ihRight =>
      intro s after step
      cases step with
      | add a b _ => exact .int (a + b)
      | binaryLeft inner => exact .add (ihLeft _ _ inner) hr
      | binaryRight _ inner => exact .add hl (ihRight _ _ inner)
  | ge hl hr ihLeft ihRight =>
      intro s after step
      cases step with
      | ge a b _ => exact .bool (a ≥ b)
      | binaryLeft inner => exact .ge (ihLeft _ _ inner) hr
      | binaryRight _ inner => exact .ge hl (ihRight _ _ inner)
  | cond hc hy hn ihTest _ _ =>
      intro s after step
      cases step with
      | ifTrue => exact hy
      | ifFalse => exact hn
      | ifStep inner => exact .cond (ihTest _ _ inner) hy hn
  | assign present he ih =>
      intro s after step
      cases step with
      | assignValue => exact .skip
      | assignStep inner => exact .assign present (ih _ _ inner)
  | deref =>
      intro s after step
      cases step with
      | deref => exact .int _
  | skip =>
      intro s after step
      cases step
  | seq hl hr ihLeft _ =>
      intro s after step
      cases step with
      | seqSkip => exact hr
      | seqStep inner => exact .seq (ihLeft _ _ inner) hr
  | loop ht hb _ _ =>
      intro s after step
      cases step with
      | «while» => exact .cond ht (.seq hb (.loop ht hb)) .skip

/-- The full preservation statement, using the alternate type proof. -/
theorem preservation_by_typing {Γ : TypeEnv} {before after : Config} {T : Ty}
    (typed : HasType Γ before.expr T)
    (covers : StoreCovers Γ before.store)
    (step : Step before after) :
    HasType Γ after.expr T ∧ StoreCovers Γ after.store :=
  ⟨preserves_type_by_typing typed before.store after step,
    step.preserves_coverage covers⟩

end Silmaril.Courses.Cambridge.L1
