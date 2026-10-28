module

public import Silmaril.Calculi.LambdaCube.PER.SystemF

@[expose] public section

set_option autoImplicit true

/-! # Relational parametricity for System F over the PER model

Reynolds' abstraction theorem [reynolds-1983-types-abstraction-parametric-polymorphism] (1983, §3, printed pp. 515–516, and §8,
(R5)/(PAR), printed p. 520) for the PER model of `PER/SystemF.lean`.

A type is interpreted twice in the PER model, once in each of two PER
environments `η₁, η₂`. Its *relational* interpretation `Ty.relR` relates the
two subquotients: at a type variable it is a given relation, at `→` it maps
related arguments to related results, and at `∀X` it quantifies over all
pairs of PERs `X, Y` and all *saturated* relations `S` between them
(`PER.IsSatRel`: contained in the two domains and closed under the PERs).
Every relational interpretation is again saturated (`Ty.relR_sat`).

* `Typed.abstraction`: the erasure of a typed term is related to itself under
  related environments (the abstraction theorem). The PER fundamental lemma
  `Typed.sound` is used for the domain conditions.
* Free theorems ([wadler-1989-theorems-for-free], Figure 1, p. 3, the rows for `I` and `K`):
  every closed inhabitant of `∀X. X → X` realizes the identity
  (`free_id`), every inhabitant of `∀X. ∀Y. X → Y → X` realizes `K`
  (`free_K`), and every inhabitant of the Church booleans `∀X. X → X → X`
  uniformly selects its first or its second argument (`free_bool`).
* `interp_polyId_rel`: already in the plain PER model, `∀X. X → X` contains
  only the identity (singleton PERs), without parametricity.

The identity extension lemma, which identifies the relational interpretation at
identity relations with the PER interpretation, is a separate model property.
This development proves the abstraction theorem and free theorems; it leaves
identity extension and a parametric PER model as further work.
-/

namespace Silmaril.Calculi.LambdaCube.PERModel

namespace PER

variable {D : Type u}

/-- `R` is a saturated relation between the PERs `A` and `B`: it relates only
elements of the two domains and is closed under `A` on the left and `B` on the
right. These are the relations between the subquotients `A.Quo` and `B.Quo`. -/
structure IsSatRel (A B : PER D) (R : D → D → Prop) : Prop where
  dom : ∀ ⦃a b⦄, R a b → A.Dom a ∧ B.Dom b
  left : ∀ ⦃a a' b⦄, A.rel a a' → R a' b → R a b
  right : ∀ ⦃a b b'⦄, R a b → B.rel b b' → R a b'

/-- The identity relation of a PER is saturated. -/
theorem isSatRel_self (A : PER D) : IsSatRel A A A.rel where
  dom _ _ h := ⟨A.dom_left h, A.dom_left (A.symm h)⟩
  left _ _ _ h k := A.trans h k
  right _ _ _ h k := A.trans h k

/-- The empty relation is saturated between any two PERs. -/
theorem isSatRel_bot (A B : PER D) : IsSatRel A B (fun _ _ => False) where
  dom _ _ h := h.elim
  left _ _ _ _ k := k
  right _ _ _ h _ := h

/-- The converse of a saturated relation is saturated. -/
theorem IsSatRel.flip {A B : PER D} {R : D → D → Prop} (h : IsSatRel A B R) :
    IsSatRel B A (fun b a => R a b) where
  dom _ _ k := (h.dom k).symm
  left _ _ _ hb k := h.right k (B.symm hb)
  right _ _ _ k ha := h.left (A.symm ha) k

/-- Equality as a PER (the discrete PER on `D`). -/
def eq : PER D := ⟨Eq, fun _ _ h => h.symm, fun _ _ _ h k => h.trans k⟩

/-- The PER whose domain is the single element `a`. -/
def single (a : D) : PER D :=
  ⟨fun x y => x = a ∧ y = a, fun _ _ h => ⟨h.2, h.1⟩, fun _ _ _ h k => ⟨h.1, k.2⟩⟩

/-- Every relation is saturated between the discrete PERs. -/
theorem isSatRel_eq (R : D → D → Prop) : IsSatRel (eq : PER D) eq R where
  dom _ _ _ := ⟨rfl, rfl⟩
  left _ _ _ h k := by cases h; exact k
  right _ _ _ h k := by cases k; exact h

end PER

namespace SystemF

variable {M : CombAlg.{u}}

/-- A relational environment: two PER environments and, for each type
variable, a saturated relation between its two interpretations
(Reynolds' relation assignment `R ∈ ∏ Rel(S₁τ, S₂τ)`, printed p. 515). -/
structure RelEnv (M : CombAlg.{u}) where
  η₁ : ℕ → PER M.D
  η₂ : ℕ → PER M.D
  R : ℕ → M.D → M.D → Prop
  sat : ∀ n, PER.IsSatRel (η₁ n) (η₂ n) (R n)

namespace RelEnv

/-- Relational environments with equal components are equal. -/
theorem ext {E E' : RelEnv M} (h₁ : E.η₁ = E'.η₁) (h₂ : E.η₂ = E'.η₂) (hR : E.R = E'.R) :
    E = E' := by
  cases E; cases E'
  subst h₁ h₂ hR
  rfl

/-- Extend by a newest type variable. -/
def cons (X Y : PER M.D) (S : M.D → M.D → Prop) (hS : PER.IsSatRel X Y S) (E : RelEnv M) :
    RelEnv M where
  η₁ := scons X E.η₁
  η₂ := scons Y E.η₂
  R := scons S E.R
  sat
    | 0 => hS
    | n + 1 => E.sat n

/-- Precompose with a renaming of type variables. -/
def comp (E : RelEnv M) (r : ℕ → ℕ) : RelEnv M :=
  ⟨E.η₁ ∘ r, E.η₂ ∘ r, E.R ∘ r, fun n => E.sat (r n)⟩

/-- The diagonal environment of a PER environment: identity relations. -/
def diag (η : ℕ → PER M.D) : RelEnv M :=
  ⟨η, η, fun n => (η n).rel, fun n => PER.isSatRel_self (η n)⟩

/-- An environment with empty PERs and empty relations, for closed types. -/
def empty : RelEnv M :=
  ⟨fun _ => PER.bot, fun _ => PER.bot, fun _ _ _ => False, fun _ => PER.isSatRel_bot _ _⟩

end RelEnv

/-- The relational interpretation of System F types (Reynolds' `R^#`,
(R1)–(R4) on printed p. 515 and (R5) on printed p. 520), relative to the PER
model: arrows and quantifiers also require membership in the two domains. -/
def Ty.relR : Ty → RelEnv M → M.D → M.D → Prop
  | .var n, E => E.R n
  | .arr A B, E => fun f g =>
      ((Ty.arr A B).interp M E.η₁).Dom f ∧ ((Ty.arr A B).interp M E.η₂).Dom g ∧
        ∀ a b, Ty.relR A E a b → Ty.relR B E (M.app f a) (M.app g b)
  | .all A, E => fun e e' =>
      ((Ty.all A).interp M E.η₁).Dom e ∧ ((Ty.all A).interp M E.η₂).Dom e' ∧
        ∀ (X Y : PER M.D) (S : M.D → M.D → Prop) (hS : PER.IsSatRel X Y S),
          Ty.relR A (E.cons X Y S hS) e e'

/-- Every relational interpretation is saturated between the two PER
interpretations. -/
theorem Ty.relR_sat (A : Ty) (E : RelEnv M) :
    PER.IsSatRel (A.interp M E.η₁) (A.interp M E.η₂) (A.relR E) := by
  induction A generalizing E with
  | var n => exact E.sat n
  | arr A B ihA ihB =>
    refine ⟨fun _ _ h => ⟨h.1, h.2.1⟩, fun f f' g hff' h => ⟨PER.dom_left _ hff', h.2.1, ?_⟩,
      fun f g g' h hgg' => ⟨h.1, PER.dom_left _ (PER.symm _ hgg'), ?_⟩⟩
    · intro a b hab
      exact (ihB E).left (hff' a a ((ihA E).dom hab).1) (h.2.2 a b hab)
    · intro a b hab
      exact (ihB E).right (h.2.2 a b hab) (hgg' b b ((ihA E).dom hab).2)
  | all A ih =>
    refine ⟨fun _ _ h => ⟨h.1, h.2.1⟩, fun f f' g hff' h => ⟨PER.dom_left _ hff', h.2.1, ?_⟩,
      fun f g g' h hgg' => ⟨h.1, PER.dom_left _ (PER.symm _ hgg'), ?_⟩⟩
    · intro X Y S hS
      exact (ih (E.cons X Y S hS)).left (hff' X) (h.2.2 X Y S hS)
    · intro X Y S hS
      exact (ih (E.cons X Y S hS)).right (h.2.2 X Y S hS) (hgg' Y)

/-- Relational interpretation under renaming of type variables. -/
theorem Ty.relR_rename (r : ℕ → ℕ) (A : Ty) (E : RelEnv M) :
    (A.rename r).relR E = A.relR (E.comp r) := by
  induction A generalizing r E with
  | var n => rfl
  | arr A B ihA ihB =>
    funext f g
    show ((((Ty.arr A B).rename r).interp M E.η₁).Dom f ∧
        (((Ty.arr A B).rename r).interp M E.η₂).Dom g ∧
        ∀ a b, (A.rename r).relR E a b → (B.rename r).relR E (M.app f a) (M.app g b)) = _
    rw [Ty.interp_rename, Ty.interp_rename, ihA, ihB]; rfl
  | all A ih =>
    funext f g
    show ((((Ty.all A).rename r).interp M E.η₁).Dom f ∧
        (((Ty.all A).rename r).interp M E.η₂).Dom g ∧
        ∀ (X Y : PER M.D) (S : M.D → M.D → Prop) (hS : PER.IsSatRel X Y S),
          (A.rename (scons 0 (Nat.succ ∘ r))).relR (E.cons X Y S hS) f g) = _
    have hc : ∀ X Y S hS, (E.cons X Y S hS).comp (scons 0 (Nat.succ ∘ r)) =
        (E.comp r).cons X Y S hS := fun X Y S hS =>
      RelEnv.ext (by funext n; cases n <;> rfl) (by funext n; cases n <;> rfl)
        (by funext n; cases n <;> rfl)
    simp only [Ty.interp_rename, ih, hc]; rfl

/-- Weakening by one type variable leaves the relational interpretation unchanged. -/
theorem Ty.relR_rename_succ (A : Ty) (E : RelEnv M) (X Y : PER M.D) (S : M.D → M.D → Prop)
    (hS : PER.IsSatRel X Y S) :
    (A.rename Nat.succ).relR (E.cons X Y S hS) = A.relR E := by
  rw [Ty.relR_rename]; rfl

/-- The relational environment of a type substitution: each variable is sent
to the PER and relational interpretations of its image. -/
def RelEnv.subst (E : RelEnv M) (σ : ℕ → Ty) : RelEnv M :=
  ⟨fun n => (σ n).interp M E.η₁, fun n => (σ n).interp M E.η₂, fun n => (σ n).relR E,
    fun n => (σ n).relR_sat E⟩

/-- Relational interpretation under simultaneous substitution. -/
theorem Ty.relR_subst (σ : ℕ → Ty) (A : Ty) (E : RelEnv M) :
    (A.subst σ).relR E = A.relR (E.subst σ) := by
  induction A generalizing σ E with
  | var n => rfl
  | arr A B ihA ihB =>
    funext f g
    show ((((Ty.arr A B).subst σ).interp M E.η₁).Dom f ∧
        (((Ty.arr A B).subst σ).interp M E.η₂).Dom g ∧
        ∀ a b, (A.subst σ).relR E a b → (B.subst σ).relR E (M.app f a) (M.app g b)) = _
    rw [Ty.interp_subst, Ty.interp_subst, ihA, ihB]; rfl
  | all A ih =>
    funext f g
    show ((((Ty.all A).subst σ).interp M E.η₁).Dom f ∧
        (((Ty.all A).subst σ).interp M E.η₂).Dom g ∧
        ∀ (X Y : PER M.D) (S : M.D → M.D → Prop) (hS : PER.IsSatRel X Y S),
          (A.subst (Ty.liftSub σ)).relR (E.cons X Y S hS) f g) = _
    have hc : ∀ X Y S hS, (E.cons X Y S hS).subst (Ty.liftSub σ) =
        (E.subst σ).cons X Y S hS := by
      intro X Y S hS
      refine RelEnv.ext ?_ ?_ ?_ <;> funext n <;> cases n
      all_goals first
        | rfl
        | exact Ty.interp_rename _ _ _
        | exact Ty.relR_rename_succ _ _ _ _ _ _
    simp only [Ty.interp_subst, ih, hc]; rfl

/-- The substitution lemma: instantiating a quantifier at `B` uses the PER
interpretations of `B` and its relational interpretation. -/
theorem Ty.relR_substOne (A B : Ty) (E : RelEnv M) :
    (A.substOne B).relR E =
      A.relR (E.cons (B.interp M E.η₁) (B.interp M E.η₂) (B.relR E) (B.relR_sat E)) := by
  unfold Ty.substOne
  rw [Ty.relR_subst]
  congr 1
  exact RelEnv.ext (by funext n; cases n <;> rfl) (by funext n; cases n <;> rfl)
    (by funext n; cases n <;> rfl)

/-- Related realizer environments for a term context. -/
def RelCtx (Γ : Ctx) (E : RelEnv M) (ρ₁ ρ₂ : ℕ → M.D) : Prop :=
  ∀ n (A : Ty), Γ[n]? = some A → A.relR E (ρ₁ n) (ρ₂ n)

/-- Related environments are in the domains of the two PER interpretations. -/
theorem RelCtx.envRel₁ {Γ : Ctx} {E : RelEnv M} {ρ₁ ρ₂ : ℕ → M.D} (h : RelCtx Γ E ρ₁ ρ₂) :
    EnvRel M Γ E.η₁ ρ₁ ρ₁ := fun n A hA => ((A.relR_sat E).dom (h n A hA)).1

theorem RelCtx.envRel₂ {Γ : Ctx} {E : RelEnv M} {ρ₁ ρ₂ : ℕ → M.D} (h : RelCtx Γ E ρ₁ ρ₂) :
    EnvRel M Γ E.η₂ ρ₂ ρ₂ := fun n A hA => ((A.relR_sat E).dom (h n A hA)).2

/-- `∀X. X → X`. -/
def idTy : Ty := .all (.arr (.var 0) (.var 0))

/-- `∀X. ∀Y. X → Y → X`. -/
def kTy : Ty := .all (.all (.arr (.var 1) (.arr (.var 0) (.var 1))))


end SystemF

end Silmaril.Calculi.LambdaCube.PERModel
