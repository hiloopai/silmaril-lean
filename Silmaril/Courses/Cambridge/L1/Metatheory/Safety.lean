module

public import Silmaril.Courses.Cambridge.L1.Metatheory.TypingUniqueness

/-! # Cambridge L1 safety (Theorem 4)

Theorem 3 composes along finite small-step traces. Progress then applies to
every reachable configuration, giving Theorem 4 on p. 47. The final statement
also uses the bridge to the shared operational LTS from §1 and §2.1.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

theorem preservation_steps {Γ : TypeEnv} {before after : Config} {T : Ty}
    (typed : HasType Γ before.expr T)
    (covers : StoreCovers Γ before.store)
    (steps : Steps before after) :
    HasType Γ after.expr T ∧ StoreCovers Γ after.store := by
  induction steps with
  | refl => exact ⟨typed, covers⟩
  | tail _ step ih => exact preservation ih.1 ih.2 step

/-- Theorem 4: no well-typed reachable L1 configuration is stuck. -/
theorem safety {Γ : TypeEnv} {before after : Config} {T : Ty}
    (typed : HasType Γ before.expr T)
    (covers : StoreCovers Γ before.store)
    (steps : Steps before after) :
    IsValue after.expr ∨ ∃ next, Step after next := by
  obtain ⟨typedAfter, coversAfter⟩ := preservation_steps typed covers steps
  exact progress typedAfter coversAfter

/-- The same safety theorem phrased through the reusable LTS reachability API. -/
theorem safety_reachable {Γ : TypeEnv} {before after : Config} {T : Ty}
    (typed : HasType Γ before.expr T)
    (covers : StoreCovers Γ before.store)
    (reachable : lts.CanReach before after) :
    IsValue after.expr ∨ ∃ next, lts.UnlabelledTr after next := by
  rcases safety typed covers (steps_iff_reachable.mpr reachable) with
    value | ⟨next, step⟩
  · exact Or.inl value
  · exact Or.inr ⟨next, lts_unlabelled_iff.mpr step⟩

end Silmaril.Courses.Cambridge.L1
