module

public import Silmaril.Courses.Cambridge.L2.Metatheory.Preservation

/-! # Cambridge L2 closedness preservation, Exercise 25

This completes Theorem 19 by proving the remaining closed-expression clause.
Scope is tracked by de Bruijn depth; free names are tracked separately. The
proof covers substitution and the rearranged binders of recursive closures.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

def ScopeRenaming (source target : Nat) (ρ : Nat → Nat) : Prop :=
  ∀ index, index < source → ρ index < target

theorem ScopeRenaming.lift {source target : Nat} {ρ : Nat → Nat}
    (compatible : ScopeRenaming source target ρ) :
    ScopeRenaming (source + 1) (target + 1) (DeBruijn.lift ρ) := by
  intro index bound
  cases index with
  | zero => exact Nat.zero_lt_succ target
  | succ index =>
      exact Nat.succ_lt_succ (compatible index (Nat.lt_of_succ_lt_succ bound))

theorem ScopeRenaming.liftTwo {source target : Nat} {ρ : Nat → Nat}
    (compatible : ScopeRenaming source target ρ) :
    ScopeRenaming (source + 2) (target + 2) (DeBruijn.liftN 2 ρ) := by
  simpa [DeBruijn.liftN, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    compatible.lift.lift

theorem Expr.scoped_rename (e : Expr) {source target : Nat} (ρ : Nat → Nat)
    (compatible : ScopeRenaming source target ρ)
    (wellScoped : e.Scoped source) : (e.rename ρ).Scoped target := by
  induction e generalizing source target ρ with
  | int | bool | deref | skip | fvar => trivial
  | bvar index => exact compatible index wellScoped
  | binary left op right ihLeft ihRight =>
      exact ⟨ihLeft ρ compatible wellScoped.1, ihRight ρ compatible wellScoped.2⟩
  | cond test yes no ihTest ihYes ihNo =>
      exact ⟨ihTest ρ compatible wellScoped.1,
        ihYes ρ compatible wellScoped.2.1, ihNo ρ compatible wellScoped.2.2⟩
  | assign loc value ih => exact ih ρ compatible wellScoped
  | seq left right ihLeft ihRight =>
      exact ⟨ihLeft ρ compatible wellScoped.1, ihRight ρ compatible wellScoped.2⟩
  | loop test body ihTest ihBody =>
      exact ⟨ihTest ρ compatible wellScoped.1, ihBody ρ compatible wellScoped.2⟩
  | lam domain body ih =>
      exact ih (DeBruijn.lift ρ) compatible.lift wellScoped
  | app function argument ihFunction ihArgument =>
      exact ⟨ihFunction ρ compatible wellScoped.1,
        ihArgument ρ compatible wellScoped.2⟩
  | letE type value body ihValue ihBody =>
      exact ⟨ihValue ρ compatible wellScoped.1,
        ihBody (DeBruijn.lift ρ) compatible.lift wellScoped.2⟩
  | letRecFun domain codomain functionBody body ihFunction ihBody =>
      exact ⟨ihFunction (DeBruijn.liftN 2 ρ) compatible.liftTwo wellScoped.1,
        ihBody (DeBruijn.lift ρ) compatible.lift wellScoped.2⟩

def ScopeSubstitution (source target : Nat) (σ : Nat → Expr) : Prop :=
  ∀ index, index < source → (σ index).Scoped target

theorem ScopeSubstitution.lift {source target : Nat} {σ : Nat → Expr}
    (compatible : ScopeSubstitution source target σ) :
    ScopeSubstitution (source + 1) (target + 1) (Expr.liftSubst σ) := by
  intro index bound
  cases index with
  | zero => exact Nat.zero_lt_succ target
  | succ index =>
      apply (σ index).scoped_rename Nat.succ
      · intro i hi
        exact Nat.succ_lt_succ hi
      · exact compatible index (Nat.lt_of_succ_lt_succ bound)

theorem ScopeSubstitution.liftTwo {source target : Nat} {σ : Nat → Expr}
    (compatible : ScopeSubstitution source target σ) :
    ScopeSubstitution (source + 2) (target + 2)
      (Expr.liftSubst (Expr.liftSubst σ)) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    compatible.lift.lift

theorem Expr.scoped_subst (e : Expr) {source target : Nat} (σ : Nat → Expr)
    (compatible : ScopeSubstitution source target σ)
    (wellScoped : e.Scoped source) : (e.subst σ).Scoped target := by
  induction e generalizing source target σ with
  | int | bool | deref | skip | fvar => trivial
  | bvar index => exact compatible index wellScoped
  | binary left op right ihLeft ihRight =>
      exact ⟨ihLeft σ compatible wellScoped.1, ihRight σ compatible wellScoped.2⟩
  | cond test yes no ihTest ihYes ihNo =>
      exact ⟨ihTest σ compatible wellScoped.1,
        ihYes σ compatible wellScoped.2.1, ihNo σ compatible wellScoped.2.2⟩
  | assign loc value ih => exact ih σ compatible wellScoped
  | seq left right ihLeft ihRight =>
      exact ⟨ihLeft σ compatible wellScoped.1, ihRight σ compatible wellScoped.2⟩
  | loop test body ihTest ihBody =>
      exact ⟨ihTest σ compatible wellScoped.1, ihBody σ compatible wellScoped.2⟩
  | lam domain body ih =>
      exact ih (Expr.liftSubst σ) compatible.lift wellScoped
  | app function argument ihFunction ihArgument =>
      exact ⟨ihFunction σ compatible wellScoped.1,
        ihArgument σ compatible wellScoped.2⟩
  | letE type value body ihValue ihBody =>
      exact ⟨ihValue σ compatible wellScoped.1,
        ihBody (Expr.liftSubst σ) compatible.lift wellScoped.2⟩
  | letRecFun domain codomain functionBody body ihFunction ihBody =>
      exact ⟨ihFunction (Expr.liftSubst (Expr.liftSubst σ))
        compatible.liftTwo wellScoped.1,
        ihBody (Expr.liftSubst σ) compatible.lift wellScoped.2⟩

theorem Expr.beta_scoped {body argument : Expr} {depth : Nat}
    (bodyScoped : body.Scoped (depth + 1))
    (argumentScoped : argument.Scoped depth) :
    (body.beta argument).Scoped depth := by
  apply body.scoped_subst (fun
    | 0 => argument
    | index + 1 => .bvar index) ?_ bodyScoped
  intro index bound
  cases index with
  | zero => exact argumentScoped
  | succ index => exact Nat.lt_of_succ_lt_succ bound

theorem Expr.recClosure_scoped {domain codomain : Ty} {functionBody : Expr}
    {depth : Nat} (wellScoped : functionBody.Scoped (depth + 2)) :
    (Expr.recClosure domain codomain functionBody).Scoped depth := by
  unfold Expr.recClosure
  constructor
  · apply functionBody.scoped_rename (DeBruijn.liftN 2 Nat.succ)
    · apply ScopeRenaming.liftTwo
      intro index bound
      exact Nat.succ_lt_succ bound
    · exact wellScoped
  · apply functionBody.scoped_rename swapFirstTwo
    · intro index bound
      cases index with
      | zero => simp [swapFirstTwo]
      | succ index =>
          cases index with
          | zero => simp [swapFirstTwo]
          | succ index => exact bound
    · exact wellScoped

def FreeSubstitution (σ : Nat → Expr) : Prop :=
  ∀ index, (σ index).freeVars = ∅

theorem FreeSubstitution.lift {σ : Nat → Expr}
    (closed : FreeSubstitution σ) :
    FreeSubstitution (Expr.liftSubst σ) := by
  intro index
  cases index with
  | zero => rfl
  | succ index => simpa [Expr.liftSubst, Expr.freeVars_rename] using closed index

theorem FreeSubstitution.liftTwo {σ : Nat → Expr}
    (closed : FreeSubstitution σ) :
    FreeSubstitution (Expr.liftSubst (Expr.liftSubst σ)) :=
  closed.lift.lift

theorem Expr.freeVars_subst_empty (e : Expr) (σ : Nat → Expr)
    (compatible : FreeSubstitution σ) (noNames : e.freeVars = ∅) :
    (e.subst σ).freeVars = ∅ := by
  induction e generalizing σ with
  | int | bool | deref | skip => rfl
  | bvar index => exact compatible index
  | fvar name => simp [Expr.freeVars] at noNames
  | binary left op right ihLeft ihRight =>
      simp only [Expr.subst, Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ihLeft σ compatible noNames.1, ihRight σ compatible noNames.2⟩
  | cond test yes no ihTest ihYes ihNo =>
      simp only [Expr.subst, Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨⟨ihTest σ compatible noNames.1.1,
        ihYes σ compatible noNames.1.2⟩, ihNo σ compatible noNames.2⟩
  | assign loc value ih => exact ih σ compatible noNames
  | seq left right ihLeft ihRight =>
      simp only [Expr.subst, Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ihLeft σ compatible noNames.1, ihRight σ compatible noNames.2⟩
  | loop test body ihTest ihBody =>
      simp only [Expr.subst, Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ihTest σ compatible noNames.1, ihBody σ compatible noNames.2⟩
  | lam domain body ih =>
      exact ih (Expr.liftSubst σ) compatible.lift noNames
  | app function argument ihFunction ihArgument =>
      simp only [Expr.subst, Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ihFunction σ compatible noNames.1,
        ihArgument σ compatible noNames.2⟩
  | letE type value body ihValue ihBody =>
      simp only [Expr.subst, Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ihValue σ compatible noNames.1,
        ihBody (Expr.liftSubst σ) compatible.lift noNames.2⟩
  | letRecFun domain codomain functionBody body ihFunction ihBody =>
      simp only [Expr.subst, Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ihFunction (Expr.liftSubst (Expr.liftSubst σ))
        compatible.liftTwo noNames.1,
        ihBody (Expr.liftSubst σ) compatible.lift noNames.2⟩

theorem Expr.beta_freeVars_empty {body argument : Expr}
    (bodyNoNames : body.freeVars = ∅)
    (argumentNoNames : argument.freeVars = ∅) :
    (body.beta argument).freeVars = ∅ := by
  apply body.freeVars_subst_empty (fun
    | 0 => argument
    | index + 1 => .bvar index) ?_ bodyNoNames
  intro index
  cases index with
  | zero => exact argumentNoNames
  | succ index => rfl

theorem Expr.recClosure_freeVars_empty {domain codomain : Ty}
    {functionBody : Expr} (noNames : functionBody.freeVars = ∅) :
    (Expr.recClosure domain codomain functionBody).freeVars = ∅ := by
  simp only [Expr.recClosure, Expr.freeVars, Finset.union_eq_empty]
  exact ⟨by simpa only [Expr.freeVars_rename] using noNames,
    by simpa only [Expr.freeVars_rename] using noNames⟩

theorem Step.preserves_scoped {before after : Config} (step : Step before after)
    {depth : Nat} (wellScoped : before.expr.Scoped depth) :
    after.expr.Scoped depth := by
  induction step generalizing depth with
  | add | ge | deref | assignValue =>
      trivial
  | binaryLeft inner ih => exact ⟨ih wellScoped.1, wellScoped.2⟩
  | binaryRight _ inner ih => exact ⟨wellScoped.1, ih wellScoped.2⟩
  | assignStep inner ih => exact ih wellScoped
  | seqSkip => exact wellScoped.2
  | seqStep inner ih => exact ⟨ih wellScoped.1, wellScoped.2⟩
  | ifTrue => exact wellScoped.2.1
  | ifFalse => exact wellScoped.2.2
  | ifStep inner ih =>
      exact ⟨ih wellScoped.1, wellScoped.2.1, wellScoped.2.2⟩
  | «while» =>
      exact ⟨wellScoped.1, ⟨wellScoped.2, wellScoped⟩, trivial⟩
  | appLeft inner ih => exact ⟨ih wellScoped.1, wellScoped.2⟩
  | appRight _ inner ih => exact ⟨wellScoped.1, ih wellScoped.2⟩
  | appFun value => exact Expr.beta_scoped wellScoped.1 wellScoped.2
  | letStep inner ih => exact ⟨ih wellScoped.1, wellScoped.2⟩
  | letValue ready => exact Expr.beta_scoped wellScoped.2 wellScoped.1
  | letRecFun =>
      exact Expr.beta_scoped wellScoped.2
        (Expr.recClosure_scoped wellScoped.1)

theorem Step.preserves_freeVars_empty {before after : Config}
    (step : Step before after) (noNames : before.expr.freeVars = ∅) :
    after.expr.freeVars = ∅ := by
  induction step with
  | add | ge | deref | assignValue => rfl
  | binaryLeft inner ih =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ih noNames.1, noNames.2⟩
  | binaryRight _ inner ih =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨noNames.1, ih noNames.2⟩
  | assignStep inner ih => exact ih noNames
  | seqSkip =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames
      exact noNames.2
  | seqStep inner ih =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ih noNames.1, noNames.2⟩
  | ifTrue =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames
      exact noNames.1.2
  | ifFalse =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames
      exact noNames.2
  | ifStep inner ih =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨⟨ih noNames.1.1, noNames.1.2⟩, noNames.2⟩
  | «while» =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      aesop
  | appLeft inner ih =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ih noNames.1, noNames.2⟩
  | appRight _ inner ih =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨noNames.1, ih noNames.2⟩
  | appFun value =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames
      exact Expr.beta_freeVars_empty noNames.1 noNames.2
  | letStep inner ih =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames ⊢
      exact ⟨ih noNames.1, noNames.2⟩
  | letValue ready =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames
      exact Expr.beta_freeVars_empty noNames.2 noNames.1
  | letRecFun =>
      simp only [Expr.freeVars, Finset.union_eq_empty] at noNames
      exact Expr.beta_freeVars_empty noNames.2
        (Expr.recClosure_freeVars_empty noNames.1)

theorem Step.preserves_closed {before after : Config}
    (step : Step before after) (closed : before.expr.Closed) :
    after.expr.Closed :=
  ⟨step.preserves_scoped closed.1,
    step.preserves_freeVars_empty closed.2⟩

/-- Theorem 19: typing, closedness, and allocated-location coverage persist. -/
theorem type_preservation {Γ : TypeEnv} {before after : Config} {T : Ty}
    (typed : HasType Γ before.expr T)
    (closed : before.expr.Closed)
    (covers : StoreCovers Γ before.store)
    (step : Step before after) :
    HasType Γ after.expr T ∧ after.expr.Closed ∧
      StoreCovers Γ after.store :=
  ⟨step.preserves_type typed, step.preserves_closed closed,
    step.preserves_coverage covers⟩

end Silmaril.Courses.Cambridge.L2
