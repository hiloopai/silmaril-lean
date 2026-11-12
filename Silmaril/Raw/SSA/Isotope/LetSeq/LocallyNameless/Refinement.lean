module

public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Equiv

/-!
# Directed refinement theories of LetSeq

Refinement is the least compatible preorder containing the equational theory
and a chosen family of directed primitive rules. No symmetry rule is added.
The empty primitive theory recovers precisely the equational theory.
The `least` and `bind` interfaces eliminate generated derivations; monotonicity
and idempotence follow without repeating induction over the syntax rules.
-/

@[expose] public section
set_option autoImplicit true

namespace Silmaril.Isotope.LetSeq.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε]

/-- A primitive directed relation on raw, scope-indexed syntax. -/
abbrev RawRelation (ν : Type u) (Φ : Type v) :=
  {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop

/-- Compatible directed closure over raw syntax. -/
inductive RawRefinement (pureEff : ε) (R : RawRelation ν Φ) :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | equiv : RawEquiv pureEff a b → RawRefinement pureEff R a b
  | primitive : R a b → RawRefinement pureEff R a b
  | trans : RawRefinement pureEff R a b → RawRefinement pureEff R b c →
      RawRefinement pureEff R a c
  | op : RawRefinement pureEff R a a' → RawRefinement pureEff R (.op f a) (.op f a')
  | let₁ : RawRefinement pureEff R a a' → RawRefinement pureEff R b b' → RawRefinement pureEff R (.let₁ a b) (.let₁ a' b')
  | pair : RawRefinement pureEff R a a' → RawRefinement pureEff R b b' → RawRefinement pureEff R (.pair a b) (.pair a' b')
  | let₂ : RawRefinement pureEff R a a' → RawRefinement pureEff R b b' → RawRefinement pureEff R (.let₂ a b) (.let₂ a' b')

namespace RawRefinement

/-- The closure conditions characterizing refinement by its leastness. -/
structure Closed (pureEff : ε) (R Q : RawRelation ν Φ) : Prop where
  equiv : RawEquiv pureEff a b → Q a b
  primitive : R a b → Q a b
  trans : Q a b → Q b c → Q a c
  op : Q a a' → Q (.op f a) (.op f a')
  let₁ : Q a a' → Q b b' → Q (.let₁ a b) (.let₁ a' b')
  pair : Q a a' → Q b b' → Q (.pair a b) (.pair a' b')
  let₂ : Q a a' → Q b b' → Q (.let₂ a b) (.let₂ a' b')

variable {pureEff : ε} {R Q : RawRelation ν Φ} {n : Nat} {a b : Tm ν Φ n}

theorem refl (a : Tm ν Φ n) : RawRefinement pureEff R a a := .equiv (.refl a)

/-- Every compatible preorder containing the generating rules contains the closure. -/
theorem least (hQ : Closed pureEff R Q) (h : RawRefinement pureEff R a b) : Q a b := by
  induction h with
  | equiv h => exact hQ.equiv h
  | primitive h => exact hQ.primitive h
  | trans h k ih ik => exact hQ.trans ih ik
  | op h0 ih0 => exact hQ.op ih0
  | let₁ h0 h1 ih0 ih1 => exact hQ.let₁ ih0 ih1
  | pair h0 h1 ih0 ih1 => exact hQ.pair ih0 ih1
  | let₂ h0 h1 ih0 ih1 => exact hQ.let₂ ih0 ih1

/-- The generated relation itself satisfies the closure conditions. -/
theorem closed : Closed pureEff R (RawRefinement pureEff R) where
  equiv := .equiv
  primitive := .primitive
  trans := .trans
  op := .op
  let₁ := .let₁
  pair := .pair
  let₂ := .let₂

/-- Replace each primitive step by a derivation in another refinement theory. -/
theorem bind (hRQ : ∀ {n} {a b : Tm ν Φ n}, R a b → RawRefinement pureEff Q a b)
    (h : RawRefinement pureEff R a b) : RawRefinement pureEff Q a b :=
  least { closed (pureEff := pureEff) (R := Q) with primitive := hRQ } h

/-- Adding primitive directed rules can only add refinements. -/
theorem monotone (hRQ : ∀ {n} {a b : Tm ν Φ n}, R a b → Q a b)
    (h : RawRefinement pureEff R a b) : RawRefinement pureEff Q a b :=
  bind (fun h => .primitive (hRQ h)) h

/-- Closing an already generated theory adds no new refinements. -/
@[simp] theorem idempotent :
    RawRefinement pureEff (RawRefinement pureEff R) a b ↔ RawRefinement pureEff R a b :=
  ⟨bind (fun h => h), .primitive⟩

/-- With no directed primitive laws, refinement is exactly equality. -/
@[simp] theorem empty_iff :
    RawRefinement pureEff (fun {_} _ _ => False) a b ↔ RawEquiv pureEff a b := by
  constructor
  · intro h
    apply least (Q := RawEquiv pureEff) _ h
    exact {
      equiv := id
      primitive := False.elim
      trans := .trans
      op := .op
      let₁ := .let₁
      pair := .pair
      let₂ := .let₂
    }
  · exact .equiv

end RawRefinement

variable {τ : Type r} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]

/-- Primitive typed relations are indexed by scope, bound context, and result type. -/
abbrev TypedRelation (ν : Type u) (Φ : Type v) (τ : Type r) :=
  {n : Nat} → BoundCtx τ n → Tm ν Φ n → Tm ν Φ n → τ → Prop

/-- Compatible directed closure with exact typing of both endpoints. -/
inductive Refinement (pureEff : ε) (Γ : Isotope.Ctx ν τ) (R : TypedRelation ν Φ τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → Tm ν Φ n → τ → Prop where
  | equiv : Equiv pureEff Γ β a b A → Refinement pureEff Γ R β a b A
  | primitive : R β a b A → HasType Φ Γ β a A → HasType Φ Γ β b A →
      Refinement pureEff Γ R β a b A
  | trans : Refinement pureEff Γ R β a b A → Refinement pureEff Γ R β b c A →
      Refinement pureEff Γ R β a c A
  | op : Refinement pureEff Γ R β a a' (instrSrc f) → Refinement pureEff Γ R β (.op f a) (.op f a') (instrTrg f)
  | let₁ : Refinement pureEff Γ R β a a' A → Refinement pureEff Γ R (.snoc β A) b b' B →
    Refinement pureEff Γ R β (.let₁ a b) (.let₁ a' b') B
  | pair : Refinement pureEff Γ R β a a' A → Refinement pureEff Γ R β b b' B →
    Refinement pureEff Γ R β (.pair a b) (.pair a' b') (product A B)
  | let₂ : Refinement pureEff Γ R β a a' (product A B) → Refinement pureEff Γ R (.snoc (.snoc β A) B) b b' C →
    Refinement pureEff Γ R β (.let₂ a b) (.let₂ a' b') C

namespace Refinement

/-- The rules an arbitrary relation must satisfy to contain the generated refinement. -/
structure Closed (pureEff : ε) (Γ : Isotope.Ctx ν τ) (R Q : TypedRelation ν Φ τ) : Prop where
  equiv : Equiv pureEff Γ β a b A → Q β a b A
  primitive : R β a b A → HasType Φ Γ β a A → HasType Φ Γ β b A → Q β a b A
  trans : Q β a b A → Q β b c A → Q β a c A
  op : Q β a a' (instrSrc f) → Q β (.op f a) (.op f a') (instrTrg f)
  let₁ : Q β a a' A → Q (.snoc β A) b b' B →
    Q β (.let₁ a b) (.let₁ a' b') B
  pair : Q β a a' A → Q β b b' B →
    Q β (.pair a b) (.pair a' b') (product A B)
  let₂ : Q β a a' (product A B) → Q (.snoc (.snoc β A) B) b b' C →
    Q β (.let₂ a b) (.let₂ a' b') C

variable {pureEff : ε} {Γ : Isotope.Ctx ν τ} {R Q : TypedRelation ν Φ τ}
variable {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}

theorem refl (h : HasType Φ Γ β a A) : Refinement pureEff Γ R β a a A :=
  .equiv (.refl h)

/-- Exact typing is invariant under the entire directed closure. -/
theorem hasType (h : Refinement pureEff Γ R β a b A) :
    HasType Φ Γ β a A ∧ HasType Φ Γ β b A := by
  induction h with
  | equiv h => exact h.hasType
  | primitive h ha hb => exact ⟨ha, hb⟩
  | trans h k ih ik => exact ⟨ih.1, ik.2⟩
  | op h0 ih0 => exact ⟨.op ih0.1, .op ih0.2⟩
  | let₁ h0 h1 ih0 ih1 => exact ⟨.let₁ ih0.1 ih1.1, .let₁ ih0.2 ih1.2⟩
  | pair h0 h1 ih0 ih1 => exact ⟨.pair ih0.1 ih1.1, .pair ih0.2 ih1.2⟩
  | let₂ h0 h1 ih0 ih1 => exact ⟨.let₂ ih0.1 ih1.1, .let₂ ih0.2 ih1.2⟩

/-- Reflexivity in a typed refinement theory is equivalent to exact typing. -/
@[simp] theorem refl_iff : Refinement pureEff Γ R β a a A ↔ HasType Φ Γ β a A :=
  ⟨fun h => h.hasType.1, refl⟩

/-- Refinement is the least relation with its stated closure properties. -/
theorem least (hQ : Closed pureEff Γ R Q) (h : Refinement pureEff Γ R β a b A) :
    Q β a b A := by
  induction h with
  | equiv h => exact hQ.equiv h
  | primitive h ha hb => exact hQ.primitive h ha hb
  | trans h k ih ik => exact hQ.trans ih ik
  | op h0 ih0 => exact hQ.op ih0
  | let₁ h0 h1 ih0 ih1 => exact hQ.let₁ ih0 ih1
  | pair h0 h1 ih0 ih1 => exact hQ.pair ih0 ih1
  | let₂ h0 h1 ih0 ih1 => exact hQ.let₂ ih0 ih1

/-- The generated typed relation satisfies all of its closure conditions. -/
theorem closed : Closed pureEff Γ R (Refinement pureEff Γ R) where
  equiv := .equiv
  primitive := .primitive
  trans := .trans
  op := .op
  let₁ := .let₁
  pair := .pair
  let₂ := .let₂

/-- Replace a typed primitive step by a derivation. Only well-typed instances
of a primitive rule need to be interpreted. -/
theorem bind (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
    R β a b A → HasType Φ Γ β a A → HasType Φ Γ β b A →
      Refinement pureEff Γ Q β a b A)
    (h : Refinement pureEff Γ R β a b A) : Refinement pureEff Γ Q β a b A :=
  least { closed (pureEff := pureEff) (Γ := Γ) (R := Q) with primitive := hRQ } h

/-- Monotonicity in the primitive theory. -/
theorem monotone (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
    R β a b A → Q β a b A) (h : Refinement pureEff Γ R β a b A) :
    Refinement pureEff Γ Q β a b A :=
  bind (fun h ha hb => .primitive (hRQ h) ha hb) h

/-- Closing a generated typed theory again adds no new refinements. -/
@[simp] theorem idempotent :
    Refinement pureEff Γ (Refinement pureEff Γ R) β a b A ↔
      Refinement pureEff Γ R β a b A :=
  ⟨bind (fun h _ _ => h), fun h => .primitive h h.hasType.1 h.hasType.2⟩

/-- No extra refinements arise in the absence of directed primitive rules. -/
@[simp] theorem empty_iff :
    Refinement pureEff Γ (fun {_} _ _ _ _ => False) β a b A ↔
      Equiv pureEff Γ β a b A := by
  constructor
  · intro h
    apply least (Q := Equiv pureEff Γ) _ h
    exact {
      equiv := id
      primitive := fun h _ _ => False.elim h
      trans := .trans
      op := .op
      let₁ := .let₁
      pair := .pair
      let₂ := .let₂
    }
  · exact .equiv

/-- Erase exact typing when each primitive refinement has a corresponding raw rule. -/
theorem toRaw {S : RawRelation ν Φ}
    (hRS : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
      R β a b A → S a b) (h : Refinement pureEff Γ R β a b A) :
    RawRefinement pureEff S a b := by
  apply least (Q := fun {_} _ a b _ => RawRefinement pureEff S a b) _ h
  exact {
    equiv := fun h => .equiv h.toRaw
    primitive := fun h _ _ => .primitive (hRS h)
    trans := .trans
    op := .op
    let₁ := .let₁
    pair := .pair
    let₂ := .let₂
  }

end Refinement

end Silmaril.Isotope.LetSeq.LocallyNameless
