module

public import Silmaril.Courses.Cambridge.L2.Metatheory.Substitution

/-! # Cambridge L2 type preservation, Exercise 25

Theorem 19 on pp. 58–59 extends L1 preservation with the application, `let`,
and recursive-function cases. The recursive case uses a typed self-reference
closure; its de Bruijn renamings preserve both the parameter and recursive
function assumptions.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

/-- The self-reference produced by `(letrecfun)` has the declared function type. -/
theorem HasType.recClosure {Γ : TypeEnv} {domain codomain : Ty}
    {functionBody : Expr}
    (bodyType : HasType ((Γ.push (.arr domain codomain)).push domain)
      functionBody codomain) :
    HasType Γ (Expr.recClosure domain codomain functionBody)
      (.arr domain codomain) := by
  unfold Expr.recClosure
  apply HasType.lam
  apply HasType.letRecFun
  · apply bodyType.rename
      (Δ := ((Γ.push domain).push (.arr domain codomain)).push domain)
      (DeBruijn.liftN 2 Nat.succ) rfl rfl
    intro index T lookup
    cases index with
    | zero =>
        simpa [TypeEnv.push, DeBruijn.liftN, DeBruijn.lift] using lookup
    | succ index =>
        cases index with
        | zero =>
            simpa [TypeEnv.push, DeBruijn.liftN, DeBruijn.lift] using lookup
        | succ index =>
            simpa [TypeEnv.push, DeBruijn.liftN, DeBruijn.lift] using lookup
  · apply bodyType.rename
      (Δ := (Γ.push domain).push (.arr domain codomain))
      swapFirstTwo rfl rfl
    intro index T lookup
    cases index with
    | zero => simpa [TypeEnv.push, swapFirstTwo] using lookup
    | succ index =>
        cases index with
        | zero => simpa [TypeEnv.push, swapFirstTwo] using lookup
        | succ index => simpa [TypeEnv.push, swapFirstTwo] using lookup

/-- The source and target stores have the same allocated locations. -/
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
  | appLeft _ ih => exact ih
  | appRight _ _ ih => exact ih
  | appFun => rfl
  | letStep _ ih => exact ih
  | letValue => rfl
  | letRecFun => rfl

def StoreCovers (Γ : TypeEnv) (s : Store) : Prop :=
  ∀ loc, loc ∈ Γ.locs → loc ∈ s

theorem Step.preserves_coverage {Γ : TypeEnv} {before after : Config}
    (step : Step before after) (covers : StoreCovers Γ before.store) :
    StoreCovers Γ after.store := by
  intro loc present
  exact (step.store_domain loc).mp (covers loc present)

/-- The type component of Theorem 19, by induction on the reduction rule. -/
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
  | appLeft inner ih =>
      cases typed with
      | app hf ha => exact .app (ih hf) ha
  | appRight _ inner ih =>
      cases typed with
      | app hf ha => exact .app hf (ih ha)
  | appFun value =>
      cases typed with
      | app hf ha =>
          cases hf with
          | lam hb => exact hb.beta ha
  | letStep inner ih =>
      cases typed with
      | letE hv hb => exact .letE (ih hv) hb
  | letValue ready =>
      cases typed with
      | letE hv hb => exact hb.beta hv
  | letRecFun =>
      cases typed with
      | letRecFun hf hb => exact hb.beta hf.recClosure

/-- Typing and store coverage remain valid after one L2 call-by-value step. -/
theorem preservation {Γ : TypeEnv} {before after : Config} {T : Ty}
    (typed : HasType Γ before.expr T)
    (covers : StoreCovers Γ before.store)
    (step : Step before after) :
    HasType Γ after.expr T ∧ StoreCovers Γ after.store :=
  ⟨step.preserves_type typed, step.preserves_coverage covers⟩

end Silmaril.Courses.Cambridge.L2
