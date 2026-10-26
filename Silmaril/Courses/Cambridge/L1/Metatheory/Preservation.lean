module

public import Silmaril.Courses.Cambridge.L1.Metatheory.Progress

/-! # Cambridge L1 type preservation and Exercise 16

Lemma 15 says a reduction does not allocate or deallocate locations. The main
proof follows the reduction derivation, inverting the source typing judgment
in each case, as on pp. 45–46. Combining the two gives Theorem 3 exactly.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

/-- Lemma 15: one step leaves the store domain unchanged. -/
theorem Step.store_domain {before after : Config} (step : Step before after)
    (loc : Loc) : loc ∈ before.store ↔ loc ∈ after.store := by
  induction step with
  | add => rfl
  | ge => rfl
  | binaryLeft _ ih => exact ih
  | binaryRight _ _ ih => exact ih
  | deref => rfl
  | assignValue present =>
      simp only [Finmap.mem_insert]
      constructor
      · exact Or.inr
      · rintro (rfl | other)
        · exact present
        · exact other
  | assignStep _ ih => exact ih
  | seqSkip => rfl
  | seqStep _ ih => exact ih
  | ifTrue => rfl
  | ifFalse => rfl
  | ifStep _ ih => exact ih
  | «while» => rfl

theorem Step.preserves_coverage {Γ : TypeEnv} {before after : Config}
    (step : Step before after) (covers : StoreCovers Γ before.store) :
    StoreCovers Γ after.store := by
  intro loc present
  exact (step.store_domain loc).mp (covers loc present)

/-- The expression-type part of Theorem 3, by induction on reduction. -/
theorem Step.preserves_type {Γ : TypeEnv} {before after : Config} {T : Ty}
    (step : Step before after) (typed : HasType Γ before.expr T) :
    HasType Γ after.expr T := by
  induction step generalizing T with
  | add left right s =>
      cases typed
      exact .int (left + right)
  | ge left right s =>
      cases typed
      exact .bool (left ≥ right)
  | binaryLeft inner ih =>
      cases typed with
      | add hl hr => exact .add (ih hl) hr
      | ge hl hr => exact .ge (ih hl) hr
  | binaryRight _ inner ih =>
      cases typed with
      | add hl hr => exact .add hl (ih hr)
      | ge hl hr => exact .ge hl (ih hr)
  | deref _ =>
      cases typed
      exact .int _
  | assignValue _ =>
      cases typed
      exact .skip
  | assignStep inner ih =>
      cases typed with
      | assign present he => exact .assign present (ih he)
  | seqSkip =>
      cases typed with
      | seq _ hr => exact hr
  | seqStep inner ih =>
      cases typed with
      | seq hl hr => exact .seq (ih hl) hr
  | ifTrue =>
      cases typed with
      | cond _ hy _ => exact hy
  | ifFalse =>
      cases typed with
      | cond _ _ hn => exact hn
  | ifStep inner ih =>
      cases typed with
      | cond hc hy hn => exact .cond (ih hc) hy hn
  | «while» =>
      cases typed with
      | loop ht hb => exact .cond ht (.seq hb (.loop ht hb)) .skip

/-- Theorem 3: both typing and allocated-location coverage are preserved. -/
theorem preservation {Γ : TypeEnv} {before after : Config} {T : Ty}
    (typed : HasType Γ before.expr T)
    (covers : StoreCovers Γ before.store)
    (step : Step before after) :
    HasType Γ after.expr T ∧ StoreCovers Γ after.store :=
  ⟨step.preserves_type typed, step.preserves_coverage covers⟩

end Silmaril.Courses.Cambridge.L1
