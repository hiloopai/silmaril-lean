module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Refinement

/-!
# Structural stability of LetIter theories

Bound renaming preserves the raw equations, including the side conditions
and the uniformity square. Exact equations additionally admit every typed
renaming and lookup-preserving weakening of the free context.
-/

@[expose] public section
set_option autoImplicit true

namespace Silmaril.Isotope.LetIter.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε]

namespace Tm

variable {n m : Nat}

@[simp] theorem rename_underBinder (ρ : Fin n → Fin m) (t : Tm ν Φ (n + 1)) :
    rename (up (up ρ)) t.underBinder = (rename (up ρ) t).underBinder := by
  rw [underBinder, rename_comp, underBinder, rename_comp]
  apply rename_congr
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem rename_underTwoBinders (ρ : Fin n → Fin m) (t : Tm ν Φ (n + 2)) :
    rename (up (up (up ρ))) t.underTwoBinders =
      (rename (up (up ρ)) t).underTwoBinders := by
  rw [underTwoBinders, rename_comp, underTwoBinders, rename_comp]
  apply rename_congr
  intro i
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

@[simp] theorem rename_instantiate (ρ : Fin n → Fin m) (b : Tm ν Φ (n + 1))
    (a : Tm ν Φ n) :
    rename ρ (instantiate b a) = instantiate (rename (up ρ) b) (rename ρ a) := by
  rw [instantiate, rename_bsubst, instantiate, bsubst_rename]
  apply bsubst_congr
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

end Tm

namespace StructuralAxiom

/-- Raw structural laws are invariant under capture-avoiding renaming. -/
theorem rename {pureEff : ε} {n m : Nat} {a b : Tm ν Φ n}
    (h : StructuralAxiom pureEff a b) (ρ : Fin n → Fin m) :
    StructuralAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b) := by
  cases h with
  | letBeta hp =>
      simpa [Tm.rename, Tm.rename_instantiate] using
        (StructuralAxiom.letBeta (b := Tm.rename (Tm.up ρ) _) (Pure.rename ρ hp))
  | letEta _ => simpa [Tm.rename, Tm.rename_lift, Tm.up] using
      (StructuralAxiom.letEta (pureEff := pureEff) _)
  | unitEta _ => simpa [Tm.rename, Tm.rename_lift, Tm.up] using
      (StructuralAxiom.unitEta (pureEff := pureEff) _)
  | pairBeta _ _ _ => simpa [Tm.rename, Tm.rename_lift, Tm.up] using
      (StructuralAxiom.pairBeta (pureEff := pureEff) _ _ _)
  | pairEta _ => exact StructuralAxiom.pairEta _
  | caseBetaL _ _ _ => simpa [Tm.rename, Tm.rename_lift, Tm.up] using
      (StructuralAxiom.caseBetaL (pureEff := pureEff) _ _ _)
  | caseBetaR _ _ _ => simpa [Tm.rename, Tm.rename_lift, Tm.up] using
      (StructuralAxiom.caseBetaR (pureEff := pureEff) _ _ _)
  | caseEta _ => simpa [Tm.rename, Tm.rename_lift, Tm.up] using
      (StructuralAxiom.caseEta (pureEff := pureEff) _)
  | emptyInitial _ _ _ => simpa [Tm.rename, Tm.rename_lift, Tm.up] using
      (StructuralAxiom.emptyInitial (pureEff := pureEff) _ _ _)

end StructuralAxiom

namespace SequencingAxiom

omit [HasEff Φ ε] in

/-- Raw commuting conversions preserve their binder placement under renaming. -/
theorem rename {pureEff : ε} {n m : Nat} {a b : Tm ν Φ n}
    (h : SequencingAxiom pureEff a b) (ρ : Fin n → Fin m) :
    SequencingAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b) := by
  cases h with
  | bindOp _ _ => simpa [Tm.rename, Tm.rename_underBinder,
      Tm.rename_underTwoBinders, Tm.up] using (SequencingAxiom.bindOp (pureEff := pureEff) _ _)
  | bindLet _ _ _ => simpa [Tm.rename, Tm.rename_underBinder,
      Tm.rename_underTwoBinders, Tm.up] using (SequencingAxiom.bindLet (pureEff := pureEff) _ _ _)
  | bindLetPair _ _ _ => simpa [Tm.rename, Tm.rename_underBinder,
      Tm.rename_underTwoBinders, Tm.up] using (SequencingAxiom.bindLetPair (pureEff := pureEff) _ _ _)
  | bindPair _ _ => simpa [Tm.rename, Tm.rename_underBinder,
      Tm.rename_underTwoBinders, Tm.up] using (SequencingAxiom.bindPair (pureEff := pureEff) _ _)
  | bindLetCase _ _ _ _ => simpa [Tm.rename, Tm.rename_underBinder,
      Tm.rename_underTwoBinders, Tm.up] using (SequencingAxiom.bindLetCase (pureEff := pureEff) _ _ _ _)
  | bindCase _ _ _ => simpa [Tm.rename, Tm.rename_underBinder,
      Tm.rename_underTwoBinders, Tm.up] using (SequencingAxiom.bindCase (pureEff := pureEff) _ _ _)

end SequencingAxiom

namespace IterationAxiom

omit [HasEff Φ ε] in

/-- Elgot axiom schemes commute with bound renaming. -/
theorem rename {pureEff : ε} {n m : Nat} {a b : Tm ν Φ n}
    (h : IterationAxiom pureEff a b) (ρ : Fin n → Fin m) :
    IterationAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b) := by
  cases h with
  | fixpoint _ _ => simpa [Tm.rename, Tm.rename_underBinder, Tm.up] using
      (IterationAxiom.fixpoint (pureEff := pureEff) _ _)
  | naturality _ _ _ => simpa [Tm.rename, Tm.rename_underBinder, Tm.up] using
      (IterationAxiom.naturality (pureEff := pureEff) _ _ _)
  | codiagonal _ _ => simpa [Tm.rename, Tm.rename_underBinder, Tm.up] using
      (IterationAxiom.codiagonal (pureEff := pureEff) _ _)
  | iterBind _ _ => simpa [Tm.rename, Tm.rename_underBinder, Tm.up] using
      (IterationAxiom.iterBind (pureEff := pureEff) _ _)

end IterationAxiom

namespace CoreAxiom

theorem rename {pureEff : ε} {n m : Nat} {a b : Tm ν Φ n}
    (h : CoreAxiom pureEff a b) (ρ : Fin n → Fin m) :
    CoreAxiom pureEff (Tm.rename ρ a) (Tm.rename ρ b) := by
  cases h with
  | structural h => exact .structural (h.rename ρ)
  | sequencing h => exact .sequencing (h.rename ρ)
  | iteration h => exact .iteration (h.rename ρ)

end CoreAxiom

namespace RawEquiv

/-- Renaming preserves the raw equational closure. -/
theorem rename {pureEff : ε} {n m : Nat} {a b : Tm ν Φ n}
    (h : RawEquiv pureEff a b) (ρ : Fin n → Fin m) :
    RawEquiv pureEff (Tm.rename ρ a) (Tm.rename ρ b) := by
  induction h generalizing m with
  | refl a => exact .refl _
  | symm h ih => exact .symm (ih ρ)
  | trans h k ih ik => exact .trans (ih ρ) (ik ρ)
  | ax h => exact .ax (h.rename ρ)
  | op h ih => exact .op (ih ρ)
  | let₁ ha hb iha ihb => exact .let₁ (iha ρ) (ihb (Tm.up ρ))
  | pair ha hb iha ihb => exact .pair (iha ρ) (ihb ρ)
  | let₂ ha hb iha ihb => exact .let₂ (iha ρ) (ihb (Tm.up (Tm.up ρ)))
  | inl h ih => exact .inl (ih ρ)
  | inr h ih => exact .inr (ih ρ)
  | case he hl hr ihe ihl ihr => exact .case (ihe ρ) (ihl (Tm.up ρ)) (ihr (Tm.up ρ))
  | abort h ih => exact .abort (ih ρ)
  | iter ha hb iha ihb => exact .iter (iha ρ) (ihb (Tm.up ρ))
  | uniformity hp square ih =>
      apply RawEquiv.uniformity (Pure.rename (Tm.up ρ) hp)
      simpa [Tm.rename, Tm.rename_underBinder, Tm.rename_instantiate, Tm.up] using
        ih (Tm.up ρ)

end RawEquiv

namespace RawRefinement

/-- Renaming is admissible when the primitive directed rules are stable under it. -/
theorem rename {pureEff : ε} {R : RawRelation ν Φ}
    (hR : ∀ {n m} {a b : Tm ν Φ n} (ρ : Fin n → Fin m),
      R a b → R (Tm.rename ρ a) (Tm.rename ρ b))
    {n m : Nat} {a b : Tm ν Φ n}
    (h : RawRefinement pureEff R a b) (ρ : Fin n → Fin m) :
    RawRefinement pureEff R (Tm.rename ρ a) (Tm.rename ρ b) := by
  induction h generalizing m with
  | equiv h => exact .equiv (h.rename ρ)
  | primitive h => exact .primitive (hR ρ h)
  | trans h k ih ik => exact .trans (ih ρ) (ik ρ)
  | op h ih => exact .op (ih ρ)
  | let₁ ha hb iha ihb => exact .let₁ (iha ρ) (ihb (Tm.up ρ))
  | pair ha hb iha ihb => exact .pair (iha ρ) (ihb ρ)
  | let₂ ha hb iha ihb => exact .let₂ (iha ρ) (ihb (Tm.up (Tm.up ρ)))
  | inl h ih => exact .inl (ih ρ)
  | inr h ih => exact .inr (ih ρ)
  | case he hl hr ihe ihl ihr => exact .case (ihe ρ) (ihl (Tm.up ρ)) (ihr (Tm.up ρ))
  | abort h ih => exact .abort (ih ρ)
  | iter ha hb iha ihb => exact .iter (iha ρ) (ihb (Tm.up ρ))

end RawRefinement

variable {τ : Type r} [TypeFormers τ] [HasTy Φ τ] [DecidableEq ν]

omit [TypeFormers τ] in
private theorem typedUp_toFun {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (ρ : TypedRenaming β β') (A : τ) :
    (TypedRenaming.up ρ A).toFun = Tm.up ρ.toFun := rfl

namespace Equiv

/-- Exact equations admit every renaming that preserves the type of each bound slot. -/
theorem rename {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n m : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ m} {a b : Tm ν Φ n} {A : τ}
    (h : Equiv pureEff Γ β a b A) (ρ : TypedRenaming β β') :
    Equiv pureEff Γ β' (Tm.rename ρ.toFun a) (Tm.rename ρ.toFun b) A := by
  induction h generalizing m with
  | refl h => exact .refl (HasType.rename ρ h)
  | symm h ih => exact .symm (ih ρ)
  | trans h k ih ik => exact .trans (ih ρ) (ik ρ)
  | ax h ha hb => exact .ax (h.rename ρ.toFun) (HasType.rename ρ ha) (HasType.rename ρ hb)
  | op h ih => exact .op (ih ρ)
  | let₁ ha hb iha ihb => exact .let₁ (iha ρ) (ihb (TypedRenaming.up ρ _))
  | unit => exact .unit
  | pair ha hb iha ihb => exact .pair (iha ρ) (ihb ρ)
  | let₂ ha hb iha ihb => exact .let₂ (iha ρ) (ihb (TypedRenaming.up (TypedRenaming.up ρ _) _))
  | inl h ih => exact .inl (ih ρ)
  | inr h ih => exact .inr (ih ρ)
  | case he hl hr ihe ihl ihr => exact .case (ihe ρ) (ihl (TypedRenaming.up ρ _)) (ihr (TypedRenaming.up ρ _))
  | abort h ih => exact .abort (ih ρ)
  | iter ha hb iha ihb => exact .iter (iha ρ) (ihb (TypedRenaming.up ρ _))
  | uniformity ha hh hp hb hb' square ih =>
      apply Equiv.uniformity (HasType.rename ρ ha) (HasType.rename (TypedRenaming.up ρ _) hh)
        (Pure.rename (Tm.up ρ.toFun) hp) (HasType.rename (TypedRenaming.up ρ _) hb)
        (HasType.rename (TypedRenaming.up ρ _) hb')
      simpa [typedUp_toFun, Tm.rename, Tm.rename_underBinder,
        Tm.rename_instantiate, Tm.up] using ih (TypedRenaming.up ρ _)

/-- Insert a fresh bound variable without changing the equation's result type. -/
theorem lift {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {a b : Tm ν Φ n} {A X : τ}
    (h : Equiv pureEff Γ β a b A) :
    Equiv pureEff Γ (.snoc β X) a.lift b.lift A :=
  h.rename (TypedRenaming.succ β X)

/-- Weaken beneath one binder, retaining the type of its bound variable. -/
theorem underBinder {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {a b : Tm ν Φ (n + 1)} {A X Y : τ}
    (h : Equiv pureEff Γ (.snoc β Y) a b A) :
    Equiv pureEff Γ (.snoc (.snoc β X) Y) a.underBinder b.underBinder A :=
  h.rename (TypedRenaming.underBinder β X Y)

/-- Weaken beneath the two variables bound by product elimination. -/
theorem underTwoBinders {pureEff : ε} {Γ : Isotope.Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {a b : Tm ν Φ (n + 2)} {A X Y Z : τ}
    (h : Equiv pureEff Γ (.snoc (.snoc β Y) Z) a b A) :
    Equiv pureEff Γ (.snoc (.snoc (.snoc β X) Y) Z)
      a.underTwoBinders b.underTwoBinders A :=
  h.rename (TypedRenaming.underTwoBinders β X Y Z)

/-- Equations are stable under free-context lookup preservation. -/
theorem weaken {pureEff : ε} {Γ Γ' : Isotope.Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : Equiv pureEff Γ β a b A)
    (hΓ : ∀ x A, Γ.lookup x = some A → Γ'.lookup x = some A) :
    Equiv pureEff Γ' β a b A := by
  induction h with
  | refl h => exact .refl (h.weaken hΓ)
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik
  | ax h ha hb => exact .ax h (ha.weaken hΓ) (hb.weaken hΓ)
  | op h ih => exact .op ih
  | let₁ ha hb iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair ha hb iha ihb => exact .pair iha ihb
  | let₂ ha hb iha ihb => exact .let₂ iha ihb
  | inl h ih => exact .inl ih
  | inr h ih => exact .inr ih
  | case he hl hr ihe ihl ihr => exact .case ihe ihl ihr
  | abort h ih => exact .abort ih
  | iter ha hb iha ihb => exact .iter iha ihb
  | uniformity ha hh hp hb hb' square ih =>
      exact .uniformity (ha.weaken hΓ) (hh.weaken hΓ) hp (hb.weaken hΓ) (hb'.weaken hΓ) ih

end Equiv

namespace Refinement

/-- Primitive stability under typed renaming lifts to the entire refinement theory. -/
theorem rename {pureEff : ε} {Γ : Isotope.Ctx ν τ} {R : TypedRelation ν Φ τ}
    (hR : ∀ {n m} {β : BoundCtx τ n} {β' : BoundCtx τ m}
      {a b : Tm ν Φ n} {A} (ρ : TypedRenaming β β'),
      R β a b A → R β' (Tm.rename ρ.toFun a) (Tm.rename ρ.toFun b) A)
    {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m} {a b : Tm ν Φ n} {A : τ}
    (h : Refinement pureEff Γ R β a b A) (ρ : TypedRenaming β β') :
    Refinement pureEff Γ R β' (Tm.rename ρ.toFun a) (Tm.rename ρ.toFun b) A := by
  induction h generalizing m with
  | equiv h => exact .equiv (h.rename ρ)
  | primitive h ha hb => exact .primitive (hR ρ h) (HasType.rename ρ ha) (HasType.rename ρ hb)
  | trans h k ih ik => exact .trans (ih ρ) (ik ρ)
  | op h ih => exact .op (ih ρ)
  | let₁ ha hb iha ihb => exact .let₁ (iha ρ) (ihb (TypedRenaming.up ρ _))
  | pair ha hb iha ihb => exact .pair (iha ρ) (ihb ρ)
  | let₂ ha hb iha ihb =>
      exact .let₂ (iha ρ) (ihb (TypedRenaming.up (TypedRenaming.up ρ _) _))
  | inl h ih => exact .inl (ih ρ)
  | inr h ih => exact .inr (ih ρ)
  | case he hl hr ihe ihl ihr =>
      exact .case (ihe ρ) (ihl (TypedRenaming.up ρ _)) (ihr (TypedRenaming.up ρ _))
  | abort h ih => exact .abort (ih ρ)
  | iter ha hb iha ihb => exact .iter (iha ρ) (ihb (TypedRenaming.up ρ _))

/-- Free-context lookup preservation leaves the primitive relation unchanged. -/
theorem weaken {pureEff : ε} {Γ Γ' : Isotope.Ctx ν τ} {R : TypedRelation ν Φ τ}
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : Refinement pureEff Γ R β a b A)
    (hΓ : ∀ x A, Γ.lookup x = some A → Γ'.lookup x = some A) :
    Refinement pureEff Γ' R β a b A := by
  apply least (Q := Refinement pureEff Γ' R) _ h
  exact {
    equiv := fun h => .equiv (h.weaken hΓ)
    primitive := fun h ha hb => .primitive h (ha.weaken hΓ) (hb.weaken hΓ)
    trans := .trans
    op := .op
    let₁ := .let₁
    pair := .pair
    let₂ := .let₂
    inl := .inl
    inr := .inr
    case := .case
    abort := .abort
    iter := .iter
  }

end Refinement

end Silmaril.Isotope.LetIter.LocallyNameless
