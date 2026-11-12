module

public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementTheory
public import Silmaril.Raw.SSA.Isotope.Theory.Contexts
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Extensions

@[expose] public section

/-!
# Contextual theories on proof-relevant typed let-case syntax

The terms in each fiber are pairs of raw syntax and an exact typing derivation.
Every constructor argument is a designated context, including binder bodies and
coercion by a fixed subtype witness. Thus contextual closure does not identify
unrelated typing or subtyping evidence.
-/

namespace Silmaril.Isotope.LetCase.ProofRelevant.LocallyNameless

open Silmaril.Isotope.LetCase.LocallyNameless (Tm)
open Silmaril.Isotope.Theory
open CategoryTheory Silmaril.Logic.Metatheory

universe u v w r

variable {ν : Type w} {Φ : Type v}
variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [DecidableEq ν] [HasTy Φ τ]

/-- A raw term with the exact proof-relevant typing derivation. -/
def TypedTerm (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  Σ a : Tm ν Φ i.depth, HasType Φ Γ i.bound a i.result

/-- Every constructor argument is also a permitted typed hole at its exact sort. -/
inductive TypedContext (Γ : Ctx ν τ) : {i j : TypingIndex τ} →
    (TypedTerm Φ Γ i → TypedTerm Φ Γ j) → Prop where
  | op {n : Nat} {β : BoundCtx τ n} {f : Φ}  :
      TypedContext Γ (i := ⟨_, β, instrSrc f⟩) (j := ⟨_, β, instrTrg f⟩)
        (fun x => ⟨.op f x.1, .op x.2⟩)
  | let₁_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc β A), B⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.let₁ x.1 b.1, .let₁ x.2 b.2⟩)
  | let₁_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β A), B⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨.let₁ a.1 x.1, .let₁ a.2 x.2⟩)
  | pair_left {n : Nat} {β : BoundCtx τ n} {A B : τ} (b : TypedTerm Φ Γ (⟨_, β, B⟩)) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, product A B⟩)
        (fun x => ⟨.pair x.1 b.1, .pair x.2 b.2⟩)
  | pair_right {n : Nat} {β : BoundCtx τ n} {A B : τ} (a : TypedTerm Φ Γ (⟨_, β, A⟩)) :
      TypedContext Γ (i := ⟨_, β, B⟩) (j := ⟨_, β, product A B⟩)
        (fun x => ⟨.pair a.1 x.1, .pair a.2 x.2⟩)
  | let₂_left {n : Nat} {β : BoundCtx τ n} {A B C : τ} (b : TypedTerm Φ Γ (⟨_, (.snoc (.snoc β A) B), C⟩)) :
      TypedContext Γ (i := ⟨_, β, product A B⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.let₂ x.1 b.1, .let₂ x.2 b.2⟩)
  | let₂_right {n : Nat} {β : BoundCtx τ n} {A B C : τ} (a : TypedTerm Φ Γ (⟨_, β, product A B⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc (.snoc β A) B), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.let₂ a.1 x.1, .let₂ a.2 x.2⟩)
  | inl {n : Nat} {β : BoundCtx τ n} {A B : τ}  :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, coprod A B⟩)
        (fun x => ⟨.inl x.1, .inl x.2⟩)
  | inr {n : Nat} {β : BoundCtx τ n} {A B : τ}  :
      TypedContext Γ (i := ⟨_, β, B⟩) (j := ⟨_, β, coprod A B⟩)
        (fun x => ⟨.inr x.1, .inr x.2⟩)
  | case_scrutinee {n : Nat} {β : BoundCtx τ n} {A B C : τ} (l : TypedTerm Φ Γ (⟨_, (.snoc β A), C⟩)) (r : TypedTerm Φ Γ (⟨_, (.snoc β B), C⟩)) :
      TypedContext Γ (i := ⟨_, β, coprod A B⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case x.1 l.1 r.1, .case x.2 l.2 r.2⟩)
  | case_left {n : Nat} {β : BoundCtx τ n} {A B C : τ} (e : TypedTerm Φ Γ (⟨_, β, coprod A B⟩)) (r : TypedTerm Φ Γ (⟨_, (.snoc β B), C⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β A), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case e.1 x.1 r.1, .case e.2 x.2 r.2⟩)
  | case_right {n : Nat} {β : BoundCtx τ n} {A B C : τ} (e : TypedTerm Φ Γ (⟨_, β, coprod A B⟩)) (l : TypedTerm Φ Γ (⟨_, (.snoc β A), C⟩)) :
      TypedContext Γ (i := ⟨_, (.snoc β B), C⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.case e.1 l.1 x.1, .case e.2 l.2 x.2⟩)
  | abort {n : Nat} {β : BoundCtx τ n} {C : τ}  :
      TypedContext Γ (i := ⟨_, β, Silmaril.empty⟩) (j := ⟨_, β, C⟩)
        (fun x => ⟨.abort x.1, .abort x.2⟩)
  | sub {n : Nat} {β : BoundCtx τ n} {A B : τ} (d : Subty A B) :
      TypedContext Γ (i := ⟨_, β, A⟩) (j := ⟨_, β, B⟩)
        (fun x => ⟨x.1, .sub x.2 d⟩)


variable {ε : Type r} [HasEff Φ ε] {pureEff : ε} {Γ : Ctx ν τ}

/-- The proof-relevant typed syntax as a genuinely contextual indexed syntax. -/
def typedSyntax (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) : IndexedSyntax where
  Index := TypingIndex τ
  Term := TypedTerm Φ Γ
  Context := TypedContext Γ

/-- Every typed constructor context preserves the existing typed equations. -/
theorem TypedContext.equations {i j : TypingIndex τ}
    {a b : TypedTerm Φ Γ i} {c : TypedTerm Φ Γ i → TypedTerm Φ Γ j}
    (hc : TypedContext Γ c) (h : TypedEquiv.Related pureEff Γ a.2 b.2) :
    TypedEquiv.Related pureEff Γ (c a).2 (c b).2 := by
  cases hc with
  | op  => exact h.map fun d => .op d
  | let₁_left b => exact h.map fun d => .let₁ d (.refl _)
  | let₁_right a => exact h.map fun d => .let₁ (.refl _) d
  | pair_left b => exact h.map fun d => .pair d (.refl _)
  | pair_right a => exact h.map fun d => .pair (.refl _) d
  | let₂_left b => exact h.map fun d => .let₂ d (.refl _)
  | let₂_right a => exact h.map fun d => .let₂ (.refl _) d
  | inl  => exact h.map fun d => .inl d
  | inr  => exact h.map fun d => .inr d
  | case_scrutinee l r => exact h.map fun d => .case d (.refl _) (.refl _)
  | case_left e r => exact h.map fun d => .case (.refl _) d (.refl _)
  | case_right e l => exact h.map fun d => .case (.refl _) (.refl _) d
  | abort  => exact h.map fun d => .abort d
  | sub s => exact h.map fun d => .sub d s

/-- Every typed constructor context preserves generated refinement. -/
theorem TypedContext.refinements {R : Refinement.Theory (Φ := Φ) Γ}
    {i j : TypingIndex τ} {a b : TypedTerm Φ Γ i}
    {c : TypedTerm Φ Γ i → TypedTerm Φ Γ j}
    (hc : TypedContext Γ c) (h : Refinement.Related pureEff Γ R a.2 b.2) :
    Refinement.Related pureEff Γ R (c a).2 (c b).2 := by
  cases hc with
  | op  => exact h.map fun d => .op d
  | let₁_left b => exact h.map fun d => .let₁ d (.refl _)
  | let₁_right a => exact h.map fun d => .let₁ (.refl _) d
  | pair_left b => exact h.map fun d => .pair d (.refl _)
  | pair_right a => exact h.map fun d => .pair (.refl _) d
  | let₂_left b => exact h.map fun d => .let₂ d (.refl _)
  | let₂_right a => exact h.map fun d => .let₂ (.refl _) d
  | inl  => exact h.map fun d => .inl d
  | inr  => exact h.map fun d => .inr d
  | case_scrutinee l r => exact h.map fun d => .case d (.refl _) (.refl _)
  | case_left e r => exact h.map fun d => .case (.refl _) d (.refl _)
  | case_right e l => exact h.map fun d => .case (.refl _) (.refl _) d
  | abort  => exact h.map fun d => .abort d
  | sub s => exact h.map fun d => .sub d s

/-- The exact typed equations are an object of the generic equational-theory category. -/
def equationalTheory (pureEff : ε) (Γ : Ctx ν τ) :
    EquationalTheory (typedSyntax Φ Γ) where
  Rel a b := TypedEquiv.Related pureEff Γ a.2 b.2
  refl a := ⟨.refl a.2⟩
  trans h k := h.elim fun d => k.elim fun e => ⟨.trans d e⟩
  congr _ hc h := hc.equations h
  symm h := h.map TypedEquiv.Deriv.symm

/-- Generated refinement is an object of the generic refinement-theory category. -/
def refinementTheory (pureEff : ε) (Γ : Ctx ν τ) (R : Refinement.Theory (Φ := Φ) Γ) :
    RefinementTheory (typedSyntax Φ Γ) where
  Rel a b := Refinement.Related pureEff Γ R a.2 b.2
  refl a := Refinement.Related.refl a.2
  trans := Refinement.Related.trans
  congr _ hc h := hc.refinements h

/-- Primitive extension induces inclusion in the contextual theory category. -/
theorem refinementTheory_mono {R S : Refinement.Theory (Φ := Φ) Γ} (h : R ≤ S) :
    refinementTheory pureEff Γ R ≤ refinementTheory pureEff Γ S :=
  fun d => d.mono h

/-- Functor from primitive theory extensions to their generated contextual theories. -/
def refinementTheoryFunctor (pureEff : ε) (Γ : Ctx ν τ) :
    Refinement.Theory (Φ := Φ) Γ ⥤ RefinementTheory (typedSyntax Φ Γ) where
  obj R := refinementTheory pureEff Γ R
  map f := CategoryTheory.homOfLE (refinementTheory_mono (fun h => (CategoryTheory.leOfHom f) h))

/-- Every refinement theory contains the existing equations in their displayed direction. -/
theorem equations_le_refinement (R : Refinement.Theory (Φ := Φ) Γ) :
    (equationalTheory pureEff Γ).toRefinementTheory ≤ refinementTheory pureEff Γ R :=
  Refinement.Related.ofEquiv

/-- The rewrite-free refinement theory is exactly the typed equational theory. -/
theorem empty_refinementTheory :
    refinementTheory pureEff Γ (Refinement.EmptyTheory (Φ := Φ) (Γ := Γ)) =
      (equationalTheory pureEff Γ).toRefinementTheory :=
  RefinementTheory.ext fun _ _ => Refinement.related_empty_iff_equiv

/-- The category of contextual equational extensions of the exact let-case equations. -/
abbrev EquationalExtensions (pureEff : ε) (Γ : Ctx ν τ) :=
  EquationalTheory.Extensions (equationalTheory (Φ := Φ) pureEff Γ)

/-- The category of contextual refinement theories containing the exact let-case equations. -/
abbrev RefinementExtensions (pureEff : ε) (Γ : Ctx ν τ) :=
  RefinementTheory.Extensions (equationalTheory (Φ := Φ) pureEff Γ).toRefinementTheory

/-- A primitive rewrite theory determines an object in the extension category. -/
def refinementExtension (pureEff : ε) (Γ : Ctx ν τ) (R : Refinement.Theory (Φ := Φ) Γ) :
    RefinementExtensions (Φ := Φ) pureEff Γ :=
  ⟨refinementTheory pureEff Γ R, equations_le_refinement R⟩


/-- Semantic elimination: any contextual preorder validating the equations and
primitive rewrites validates every generated refinement. Its relation may be
pulled back from an ordered denotational model, without identifying witnesses. -/
theorem Refinement.Deriv.sound_contextual
    (Q : RefinementTheory (typedSyntax Φ Γ))
    (heq : (equationalTheory pureEff Γ).toRefinementTheory ≤ Q)
    {R : Refinement.Theory (Φ := Φ) Γ}
    (hR : ∀ {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A},
      R.rel ha hb → Q.Rel (i := ⟨n, β, A⟩) ⟨a, ha⟩ ⟨b, hb⟩)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : Refinement.Deriv pureEff Γ R ha hb) :
    Q.Rel (i := ⟨n, β, A⟩) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction d with
  | refl h => exact Q.refl _
  | trans d e ihd ihe => exact Q.trans ihd ihe
  | «axiom» h => exact hR h
  | equiv h => exact heq ⟨h⟩
  | sub h s ih => exact Q.congr _ (.sub s) ih
  | op h ih => exact Q.congr _ (.op) ih
  | let₁ d e ihd ihe =>
    exact Q.congr₂ _ (fun b => .let₁_left b) (fun a => .let₁_right a) ihd ihe
  | pair d e ihd ihe =>
    exact Q.congr₂ _ (fun b => .pair_left b) (fun a => .pair_right a) ihd ihe
  | let₂ d e ihd ihe =>
    exact Q.congr₂ _ (fun b => .let₂_left b) (fun a => .let₂_right a) ihd ihe
  | inl h ih => exact Q.congr _ (.inl) ih
  | inr h ih => exact Q.congr _ (.inr) ih
  | «case» d l r ihd ihl ihr =>
    exact Q.congr₃ _ (fun l r => .case_scrutinee l r)
      (fun e r => .case_left e r) (fun e l => .case_right e l) ihd ihl ihr
  | abort h ih => exact Q.congr _ (.abort) ih
/-- The generated contextual refinement theory is least among all theories
validating the equations and primitive rewrites. -/
theorem refinementTheory_le_iff (Q : RefinementTheory (typedSyntax Φ Γ))
    (R : Refinement.Theory (Φ := Φ) Γ) :
    refinementTheory pureEff Γ R ≤ Q ↔
      (equationalTheory pureEff Γ).toRefinementTheory ≤ Q ∧
      (∀ {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
        {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A},
        R.rel ha hb → Q.Rel (i := ⟨n, β, A⟩) ⟨a, ha⟩ ⟨b, hb⟩) := by
  constructor
  · intro h
    exact ⟨fun d => h (Refinement.Related.ofEquiv d), fun d => h ⟨.«axiom» d⟩⟩
  · rintro ⟨heq, hR⟩ i a b h
    exact h.elim fun d => d.sound_contextual Q (fun h => heq h) (fun h => hR h)

end Silmaril.Isotope.LetCase.ProofRelevant.LocallyNameless
