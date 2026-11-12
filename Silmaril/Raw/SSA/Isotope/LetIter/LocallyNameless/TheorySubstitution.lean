module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.TheoryStructural

/-!
# Pure substitution in the LetIter theories

Substitution preserves equations when each replacement is pure and has the
exact type of its source slot. Purity protects both the let-beta premise and,
for iteration, the comparison used by uniformity. Directed theories additionally
require their primitive rules to be stable under the same substitutions.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.LetIter.LocallyNameless

namespace Tm

variable {ν : Type u} {Φ : Type v} {n m : Nat}

@[simp] theorem bsubst_underBinder (σ : Fin n → Tm ν Φ m)
    (t : Tm ν Φ (n + 1)) :
    bsubst (upSub (upSub σ)) t.underBinder =
      (bsubst (upSub σ) t).underBinder := by
  rw [underBinder, bsubst_rename, underBinder, rename_bsubst]
  apply bsubst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [upSub]
  change (σ j).lift.lift = rename (up Fin.succ) (σ j).lift
  exact (rename_lift Fin.succ (σ j)).symm

@[simp] theorem bsubst_underTwoBinders (σ : Fin n → Tm ν Φ m)
    (t : Tm ν Φ (n + 2)) :
    bsubst (upSub (upSub (upSub σ))) t.underTwoBinders =
      (bsubst (upSub (upSub σ)) t).underTwoBinders := by
  rw [underTwoBinders, bsubst_rename, underTwoBinders, rename_bsubst]
  apply bsubst_congr
  intro i
  refine Fin.cases rfl (Fin.cases rfl (fun j => ?_)) i
  simp only [upSub]
  have h := ((rename_lift (up Fin.succ) (Tm.lift (σ j))).trans
    (congrArg Tm.lift (rename_lift Fin.succ (σ j)))).symm
  convert h using 1 <;> apply rename_congr <;> intro x <;>
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) x

private theorem bsubst_drop_lift (a t : Tm ν Φ n) :
    bsubst (Fin.cases a (fun i => .bv i)) t.lift = t := by
  rw [lift, bsubst_rename]
  calc
    bsubst (fun i => Fin.cases a (fun i => .bv i) i.succ) t =
        bsubst (fun i => .bv i) t := by
          apply bsubst_congr
          intro i
          rfl
    _ = rename (fun i => i) t := bsubst_bv_eq_rename _ _
    _ = t := rename_id _

@[simp] theorem bsubst_instantiate (σ : Fin n → Tm ν Φ m)
    (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) :
    bsubst σ (instantiate b a) =
      instantiate (bsubst (upSub σ) b) (bsubst σ a) := by
  rw [instantiate, bsubst_comp, instantiate, bsubst_comp]
  apply bsubst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [upSub]
  change σ j = bsubst _ (σ j).lift
  exact (bsubst_drop_lift _ _).symm

end Tm

variable {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε]
variable {pureEff : ε}

/-- Each bound-variable replacement is syntactically pure. -/
def PureSubst {n m : Nat} (pureEff : ε) (σ : Fin n → Tm ν Φ m) : Prop :=
  ∀ i, Pure pureEff (σ i)

namespace PureSubst

/-- Extend a pure substitution beneath a binder. -/
theorem up {n m : Nat} {σ : Fin n → Tm ν Φ m}
    (hσ : PureSubst pureEff σ) : PureSubst pureEff (Tm.upSub σ) :=
  Fin.cases .bv (fun i => (hσ i).lift)

end PureSubst

namespace StructuralAxiom

/-- Pure substitutions preserve every structural axiom, including pure beta. -/
theorem bsubst {n m : Nat} {a b : Tm ν Φ n} {σ : Fin n → Tm ν Φ m}
    (h : StructuralAxiom pureEff a b) (hσ : PureSubst pureEff σ) :
    StructuralAxiom pureEff (Tm.bsubst σ a) (Tm.bsubst σ b) := by
  cases h with
  | letBeta hp =>
      simpa only [Tm.bsubst, Tm.bsubst_instantiate] using
        (StructuralAxiom.letBeta (b := Tm.bsubst (Tm.upSub σ) _) (Pure.bsubst hσ hp))
  | letEta _ => exact .letEta _
  | unitEta _ => exact .unitEta _
  | pairBeta a b c =>
      simpa only [Tm.bsubst, Tm.bsubst_lift] using
        (StructuralAxiom.pairBeta (pureEff := pureEff)
          (Tm.bsubst σ a) (Tm.bsubst σ b) (Tm.bsubst (Tm.upSub (Tm.upSub σ)) c))
  | pairEta _ => exact .pairEta _
  | caseBetaL e l r => exact .caseBetaL _ _ _
  | caseBetaR e l r => exact .caseBetaR _ _ _
  | caseEta e => exact .caseEta _
  | emptyInitial a b c => exact .emptyInitial _ _ _

end StructuralAxiom

namespace SequencingAxiom

omit [HasEff Φ ε] in
/-- Sequencing laws commute with arbitrary simultaneous substitutions. -/
theorem bsubst {n m : Nat} {a b : Tm ν Φ n}
    (h : SequencingAxiom pureEff a b) (σ : Fin n → Tm ν Φ m) :
    SequencingAxiom pureEff (Tm.bsubst σ a) (Tm.bsubst σ b) := by
  cases h with
  | bindOp _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (SequencingAxiom.bindOp (pureEff := pureEff) _ _)
  | bindLet _ _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (SequencingAxiom.bindLet (pureEff := pureEff) _ _ _)
  | bindLetPair _ _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (SequencingAxiom.bindLetPair (pureEff := pureEff) _ _ _)
  | bindPair _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (SequencingAxiom.bindPair (pureEff := pureEff) _ _)
  | bindLetCase _ _ _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (SequencingAxiom.bindLetCase (pureEff := pureEff) _ _ _ _)
  | bindCase _ _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (SequencingAxiom.bindCase (pureEff := pureEff) _ _ _)

end SequencingAxiom

namespace IterationAxiom

omit [HasEff Φ ε] in
/-- Every unconditional iteration law commutes with simultaneous substitution. -/
theorem bsubst {n m : Nat} {a b : Tm ν Φ n}
    (h : IterationAxiom pureEff a b) (σ : Fin n → Tm ν Φ m) :
    IterationAxiom pureEff (Tm.bsubst σ a) (Tm.bsubst σ b) := by
  cases h with
  | fixpoint _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (IterationAxiom.fixpoint (pureEff := pureEff) _ _)
  | naturality _ _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (IterationAxiom.naturality (pureEff := pureEff) _ _ _)
  | codiagonal _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (IterationAxiom.codiagonal (pureEff := pureEff) _ _)
  | iterBind _ _ =>
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_underTwoBinders, Tm.upSub, Fin.cases_zero] using
        (IterationAxiom.iterBind (pureEff := pureEff) _ _)

end IterationAxiom

namespace CoreAxiom

theorem bsubst {n m : Nat} {a b : Tm ν Φ n} {σ : Fin n → Tm ν Φ m}
    (h : CoreAxiom pureEff a b) (hσ : PureSubst pureEff σ) :
    CoreAxiom pureEff (Tm.bsubst σ a) (Tm.bsubst σ b) := by
  cases h with
  | structural h => exact .structural (h.bsubst hσ)
  | sequencing h => exact .sequencing (h.bsubst σ)
  | iteration h => exact .iteration (h.bsubst σ)

end CoreAxiom

namespace RawEquiv

/-- The raw equational closure is stable under pointwise-pure substitution. -/
theorem bsubst {n m : Nat} {a b : Tm ν Φ n} {σ : Fin n → Tm ν Φ m}
    (h : RawEquiv pureEff a b) (hσ : PureSubst pureEff σ) :
    RawEquiv pureEff (Tm.bsubst σ a) (Tm.bsubst σ b) := by
  induction h generalizing m with
  | refl a => exact .refl _
  | symm h ih => exact .symm (ih hσ)
  | trans h k ih ik => exact .trans (ih hσ) (ik hσ)
  | ax h => exact .ax (h.bsubst hσ)
  | op h ih => exact .op (ih hσ)
  | let₁ ha hb iha ihb => exact .let₁ (iha hσ) (ihb hσ.up)
  | pair ha hb iha ihb => exact .pair (iha hσ) (ihb hσ)
  | let₂ ha hb iha ihb => exact .let₂ (iha hσ) (ihb hσ.up.up)
  | inl h ih => exact .inl (ih hσ)
  | inr h ih => exact .inr (ih hσ)
  | case he hl hr ihe ihl ihr => exact .case (ihe hσ) (ihl hσ.up) (ihr hσ.up)
  | abort h ih => exact .abort (ih hσ)
  | iter ha hb iha ihb => exact .iter (iha hσ) (ihb hσ.up)
  | uniformity hp square ih =>
      apply RawEquiv.uniformity (Pure.bsubst hσ.up hp)
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_instantiate, Tm.upSub, Fin.cases_zero] using
        ih hσ.up

/-- Open an equation beneath its newest binder by a pure term. -/
theorem instantiate {n : Nat} {a : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)}
    (h : RawEquiv pureEff b b') (hp : Pure pureEff a) :
    RawEquiv pureEff (Tm.instantiate b a) (Tm.instantiate b' a) := by
  apply h.bsubst
  exact fun i => Fin.cases hp (fun _ => .bv) i

end RawEquiv

namespace RawRefinement

/-- Substitution stability of primitive directed rules extends to their closure. -/
theorem bsubst {R : RawRelation ν Φ}
    (hR : ∀ {n m : Nat} {a b : Tm ν Φ n} {σ : Fin n → Tm ν Φ m},
      PureSubst pureEff σ → R a b → R (Tm.bsubst σ a) (Tm.bsubst σ b))
    {n m : Nat} {a b : Tm ν Φ n} {σ : Fin n → Tm ν Φ m}
    (h : RawRefinement pureEff R a b) (hσ : PureSubst pureEff σ) :
    RawRefinement pureEff R (Tm.bsubst σ a) (Tm.bsubst σ b) := by
  induction h generalizing m with
  | equiv h => exact .equiv (h.bsubst hσ)
  | primitive h => exact .primitive (hR hσ h)
  | trans h k ih ik => exact .trans (ih hσ) (ik hσ)
  | op h ih => exact .op (ih hσ)
  | let₁ ha hb iha ihb => exact .let₁ (iha hσ) (ihb hσ.up)
  | pair ha hb iha ihb => exact .pair (iha hσ) (ihb hσ)
  | let₂ ha hb iha ihb => exact .let₂ (iha hσ) (ihb hσ.up.up)
  | inl h ih => exact .inl (ih hσ)
  | inr h ih => exact .inr (ih hσ)
  | case he hl hr ihe ihl ihr => exact .case (ihe hσ) (ihl hσ.up) (ihr hσ.up)
  | abort h ih => exact .abort (ih hσ)
  | iter ha hb iha ihb => exact .iter (iha hσ) (ihb hσ.up)

end RawRefinement

variable {τ : Type r} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Substitution data preserving both exact typing and every purity side condition. -/
structure PureTypedSubst (pureEff : ε) (Γ : Isotope.Ctx ν τ) {n m : Nat}
    (β : BoundCtx τ n) (β' : BoundCtx τ m) (σ : Fin n → Tm ν Φ m) : Prop where
  typed : TypedSubst (Γ := Γ) β β' σ
  pure : PureSubst pureEff σ

namespace PureTypedSubst

variable {Γ : Isotope.Ctx ν τ}

/-- Extend a substitution by the new variable at its exact binder type. -/
theorem up {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : PureTypedSubst pureEff Γ β β' σ) (A : τ) :
    PureTypedSubst pureEff Γ (.snoc β A) (.snoc β' A) (Tm.upSub σ) where
  typed := s.typed.up A
  pure := s.pure.up

/-- Compose pure typed substitutions in the same order as raw substitution. -/
theorem comp {n m k : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {β'' : BoundCtx τ k} {σ : Fin n → Tm ν Φ m} {θ : Fin m → Tm ν Φ k}
    (s : PureTypedSubst pureEff Γ β β' σ) (t : PureTypedSubst pureEff Γ β' β'' θ) :
    PureTypedSubst pureEff Γ β β'' (fun i => Tm.bsubst θ (σ i)) where
  typed := fun i => HasType.bsubst t.typed (s.typed i)
  pure := fun i => Pure.bsubst t.pure (s.pure i)

/-- The pure substitution opening the newest bound variable. -/
theorem inst {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
    (ha : HasType Φ Γ β a A) (hp : Pure pureEff a) :
    PureTypedSubst pureEff Γ (.snoc β A) β (Fin.cases a (fun i => .bv i)) where
  typed := Fin.cases ha (fun _ => .bv)
  pure := Fin.cases hp (fun _ => .bv)

end PureTypedSubst

namespace Equiv

/-- Pure exact substitutions preserve every equation, including uniformity. -/
theorem bsubst {Γ : Isotope.Ctx ν τ} {n m : Nat}
    {β : BoundCtx τ n} {β' : BoundCtx τ m} {a b : Tm ν Φ n} {A : τ}
    {σ : Fin n → Tm ν Φ m} (h : Equiv pureEff Γ β a b A)
    (s : PureTypedSubst pureEff Γ β β' σ) :
    Equiv pureEff Γ β' (Tm.bsubst σ a) (Tm.bsubst σ b) A := by
  induction h generalizing m with
  | refl h => exact .refl (HasType.bsubst s.typed h)
  | symm h ih => exact .symm (ih s)
  | trans h k ih ik => exact .trans (ih s) (ik s)
  | op h ih => exact .op (ih s)
  | let₁ ha hb iha ihb => exact .let₁ (iha s) (ihb (s.up _))
  | unit => exact .unit
  | pair ha hb iha ihb => exact .pair (iha s) (ihb s)
  | let₂ ha hb iha ihb => exact .let₂ (iha s) (ihb ((s.up _).up _))
  | ax h ha hb => exact .ax (h.bsubst s.pure) (HasType.bsubst s.typed ha) (HasType.bsubst s.typed hb)
  | inl h ih => exact .inl (ih s)
  | inr h ih => exact .inr (ih s)
  | case he hl hr ihe ihl ihr => exact .case (ihe s) (ihl (s.up _)) (ihr (s.up _))
  | abort h ih => exact .abort (ih s)
  | iter ha hb iha ihb => exact .iter (iha s) (ihb (s.up _))
  | uniformity ha hh hp hb hb' square ih =>
      apply Equiv.uniformity
        (HasType.bsubst s.typed ha)
        (HasType.bsubst (s.typed.up _) hh)
        (Pure.bsubst s.pure.up hp)
        (HasType.bsubst (s.typed.up _) hb)
        (HasType.bsubst (s.typed.up _) hb')
      simpa only [Tm.bsubst, Tm.bsubst_underBinder, Tm.bsubst_instantiate, Tm.upSub, Fin.cases_zero] using
        ih (s.up _)

/-- Pure instantiation preserves an equation under its newest binder. -/
theorem instantiate {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)} {A B : τ}
    (h : Equiv pureEff Γ (.snoc β A) b b' B)
    (ha : HasType Φ Γ β a A) (hp : Pure pureEff a) :
    Equiv pureEff Γ β (Tm.instantiate b a) (Tm.instantiate b' a) B :=
  h.bsubst (PureTypedSubst.inst ha hp)

end Equiv

namespace Refinement

/-- Pure typed substitution is admissible when the primitive theory supports it. -/
theorem bsubst {Γ : Isotope.Ctx ν τ} {R : TypedRelation ν Φ τ}
    (hR : ∀ {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
      {a b : Tm ν Φ n} {A : τ} {σ : Fin n → Tm ν Φ m},
      PureTypedSubst pureEff Γ β β' σ → R β a b A →
        R β' (Tm.bsubst σ a) (Tm.bsubst σ b) A)
    {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {a b : Tm ν Φ n} {A : τ} {σ : Fin n → Tm ν Φ m}
    (h : Refinement pureEff Γ R β a b A) (s : PureTypedSubst pureEff Γ β β' σ) :
    Refinement pureEff Γ R β' (Tm.bsubst σ a) (Tm.bsubst σ b) A := by
  induction h generalizing m with
  | equiv h => exact .equiv (h.bsubst s)
  | primitive h ha hb =>
      exact .primitive (hR s h) (HasType.bsubst s.typed ha) (HasType.bsubst s.typed hb)
  | trans h k ih ik => exact .trans (ih s) (ik s)
  | op h ih => exact .op (ih s)
  | let₁ ha hb iha ihb => exact .let₁ (iha s) (ihb (s.up _))
  | pair ha hb iha ihb => exact .pair (iha s) (ihb s)
  | let₂ ha hb iha ihb => exact .let₂ (iha s) (ihb ((s.up _).up _))
  | inl h ih => exact .inl (ih s)
  | inr h ih => exact .inr (ih s)
  | case he hl hr ihe ihl ihr => exact .case (ihe s) (ihl (s.up _)) (ihr (s.up _))
  | abort h ih => exact .abort (ih s)
  | iter ha hb iha ihb => exact .iter (iha s) (ihb (s.up _))

end Refinement

end Silmaril.Isotope.LetIter.LocallyNameless
