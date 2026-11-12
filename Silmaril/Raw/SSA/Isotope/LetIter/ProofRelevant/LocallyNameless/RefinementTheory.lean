module

public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.RefinementOrder

@[expose] public section

/-!
# Extension and substitution of proof-relevant refinement theories

Primitive rewrites can be replaced by derivations, with all endpoint typing and
subtype witnesses retained. In particular, extending a primitive theory induces
maps on derivations, relatedness, and its ordered syntax.
-/

namespace Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless.Refinement

open Silmaril.Isotope.LetIter.LocallyNameless

universe u w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]
variable {pureEff : ε} {Γ : Isotope.Ctx ν τ}

/-- Inclusion of primitive rewrites retains the exact endpoint derivations. -/
instance : LE (Theory (Φ := Φ) Γ) where
  le R S := ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}, R.rel ha hb → S.rel ha hb

instance : PartialOrder (Theory (Φ := Φ) Γ) where
  le_refl _ := fun h => h
  le_trans _ _ _ h k := fun d => k (h d)
  le_antisymm R S h k := by
    cases R with | mk rr =>
      cases S with | mk sr =>
        congr
        funext n β a b A ha hb
        exact propext ⟨h, k⟩

variable {R S T : Theory (Φ := Φ) Γ}

/-- Substitute a derivation for every primitive rewrite. This is stronger than
monotonicity and gives the elimination principle for the generated theory. -/
def Deriv.bind
    (f : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A},
      R.rel ha hb → Deriv pureEff Γ S ha hb) :
    {n : Nat} → {β : BoundCtx τ n} → {a b : Tm ν Φ n} → {A : τ} →
    {ha : HasType Φ Γ β a A} → {hb : HasType Φ Γ β b A} →
    Deriv pureEff Γ R ha hb → Deriv pureEff Γ S ha hb
  | _, _, _, _, _, _, _, .refl h => .refl h
  | _, _, _, _, _, _, _, .trans h k => .trans (h.bind f) (k.bind f)
  | _, _, _, _, _, _, _, .«axiom» h => f h
  | _, _, _, _, _, _, _, .equiv h => .equiv h
  | _, _, _, _, _, _, _, .sub h d => .sub (h.bind f) d
  | _, _, _, _, _, _, _, .op h => .op (h.bind f)
  | _, _, _, _, _, _, _, .let₁ h k => .let₁ (h.bind f) (k.bind f)
  | _, _, _, _, _, _, _, .pair h k => .pair (h.bind f) (k.bind f)
  | _, _, _, _, _, _, _, .let₂ h k => .let₂ (h.bind f) (k.bind f)
  | _, _, _, _, _, _, _, .inl h => .inl (h.bind f)
  | _, _, _, _, _, _, _, .inr h => .inr (h.bind f)
  | _, _, _, _, _, _, _, .case h l r => .case (h.bind f) (l.bind f) (r.bind f)
  | _, _, _, _, _, _, _, .abort h => .abort (h.bind f)
  | _, _, _, _, _, _, _, .iter h k => .iter (h.bind f) (k.bind f)

/-- Replacing every primitive rewrite by itself preserves the exact derivation. -/
@[simp] theorem Deriv.bind_id {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : Deriv pureEff Γ R ha hb) : d.bind (fun h => .«axiom» h) = d := by
  induction d <;> simp_all only [bind]

/-- Successive substitutions compose without changing typing or subtype witnesses. -/
@[simp] theorem Deriv.bind_comp
    (f : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A},
      R.rel ha hb → Deriv pureEff Γ S ha hb)
    (g : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A},
      S.rel ha hb → Deriv pureEff Γ T ha hb)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : Deriv pureEff Γ R ha hb) :
    (d.bind f).bind g = d.bind (fun h => (f h).bind g) := by
  induction d <;> simp_all only [bind]

/-- Extend the primitive rewrite theory without changing any proof indices. -/
def Deriv.map (f : R ≤ S) {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : Deriv pureEff Γ R ha hb) : Deriv pureEff Γ S ha hb :=
  d.bind (fun h => .«axiom» (f h))

@[simp] theorem Deriv.map_id {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : Deriv pureEff Γ R ha hb) : d.map (fun h => h) = d :=
  d.bind_id

@[simp] theorem Deriv.map_comp (f : R ≤ S) (g : S ≤ T)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : Deriv pureEff Γ R ha hb) :
    (d.map f).map g = d.map (fun h => g (f h)) :=
  d.bind_comp (fun h => .«axiom» (f h)) (fun h => .«axiom» (g h))

theorem Related.mono (f : R ≤ S)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : Related pureEff Γ R ha hb) : Related pureEff Γ S ha hb :=
  h.map (Deriv.map f)

/-- The generated theory, with primitive rules replaced by derivable rewrites. -/
def Theory.closure (pureEff : ε) (R : Theory (Φ := Φ) Γ) : Theory (Φ := Φ) Γ where
  rel := Related pureEff Γ R

theorem Theory.le_closure : R ≤ R.closure pureEff := fun h => ⟨.«axiom» h⟩

theorem Theory.closure_mono (h : R ≤ S) : R.closure pureEff ≤ S.closure pureEff :=
  fun d => d.mono h

/-- A second closure adds no refinements. The choice is at fixed exact typing
indices, so no proof irrelevance of typing or subtype witnesses is needed. -/
theorem Theory.closure_idempotent : (R.closure pureEff).closure pureEff = R.closure pureEff := by
  apply le_antisymm
  · intro n β a b A ha hb h
    exact h.elim fun d => ⟨d.bind (S := R) (fun h => Classical.choice h)⟩
  · exact Theory.le_closure

/-- Extension acts monotonically on the typed presentation. -/
def Presentation.map (f : R ≤ S) {n : Nat} {β : BoundCtx τ n} {A : τ} :
    Presentation pureEff Γ R β A →o Presentation pureEff Γ S β A where
  toFun a := ⟨a.term, a.typing⟩
  monotone' := fun _ _ h => h.mono f


/-- Extension descends to the partially ordered syntactic quotient. -/
def OrderedSyntax.map (f : R ≤ S) {n : Nat} {β : BoundCtx τ n} {A : τ} :
    OrderedSyntax pureEff Γ R β A →o OrderedSyntax pureEff Γ S β A :=
  (Presentation.map f).antisymmetrization

@[simp] theorem OrderedSyntax.map_mk (f : R ≤ S)
    {n : Nat} {β : BoundCtx τ n} {A : τ} (a : Presentation pureEff Γ R β A) :
    OrderedSyntax.map f a.toOrderedSyntax = (Presentation.map f a).toOrderedSyntax := rfl

@[simp] theorem OrderedSyntax.map_id {n : Nat} {β : BoundCtx τ n} {A : τ}
    (a : OrderedSyntax pureEff Γ R β A) : OrderedSyntax.map (fun h => h) a = a := by
  refine Quotient.inductionOn' a ?_
  intro a
  rfl

@[simp] theorem OrderedSyntax.map_comp (f : R ≤ S) (g : S ≤ T)
    {n : Nat} {β : BoundCtx τ n} {A : τ} (a : OrderedSyntax pureEff Γ R β A) :
    OrderedSyntax.map g (OrderedSyntax.map f a) = OrderedSyntax.map (fun h => g (f h)) a := by
  refine Quotient.inductionOn' a ?_
  intro a
  rfl

end Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless.Refinement
