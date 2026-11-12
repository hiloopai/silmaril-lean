module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModel
public import Silmaril.Raw.SSA.Isotope.Theory.Contexts
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementCategories
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-!
# Operation algebras and the exact syntactic model of LetCase

Every constructor acts as an operation, with binder bodies placed at their
extended context sorts. The free operation algebra uses data-valued exact
typing derivations. Every subtype witness is an explicit operation symbol;
neither equations nor refinement silently identifies distinct coercion paths.
-/

@[expose] public section
set_option autoImplicit true

universe u v w r

namespace Silmaril.Isotope.LetCase.ProofRelevant.LocallyNameless.Models

open Silmaril.Isotope.LetCase.LocallyNameless (Tm)
open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory
open Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory.TheoryModel

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ]

/-- One operation for each exact typing constructor. -/
inductive Operation (Γ : Ctx ν τ) : TypingIndex τ → Type (max u v w) where
  | fv {n : Nat} {β : BoundCtx τ n} {x : ν} {A : τ}
      (h : Γ.lookup x = some A) : Operation Γ ⟨n, β, A⟩
  | bv {n : Nat} {β : BoundCtx τ n} (i : Fin n) : Operation Γ ⟨n, β, β.get i⟩
  | op {n : Nat} {β : BoundCtx τ n} (f : Φ) : Operation Γ ⟨n, β, instrTrg f⟩
  | let₁ {n : Nat} {β : BoundCtx τ n} (A B : τ) : Operation Γ ⟨n, β, B⟩
  | unit {n : Nat} {β : BoundCtx τ n} : Operation Γ ⟨n, β, Silmaril.unit⟩
  | pair {n : Nat} {β : BoundCtx τ n} (A B : τ) : Operation Γ ⟨n, β, product A B⟩
  | let₂ {n : Nat} {β : BoundCtx τ n} (A B C : τ) : Operation Γ ⟨n, β, C⟩
  | inl {n : Nat} {β : BoundCtx τ n} (A B : τ) : Operation Γ ⟨n, β, coprod A B⟩
  | inr {n : Nat} {β : BoundCtx τ n} (A B : τ) : Operation Γ ⟨n, β, coprod A B⟩
  | case {n : Nat} {β : BoundCtx τ n} (A B C : τ) : Operation Γ ⟨n, β, C⟩
  | abort {n : Nat} {β : BoundCtx τ n} (C : τ) : Operation Γ ⟨n, β, C⟩
  | sub {n : Nat} {β : BoundCtx τ n} {A B : τ} (d : Subty A B) : Operation Γ ⟨n, β, B⟩

namespace Operation

variable {Γ : Ctx ν τ}

abbrev arity : {i : TypingIndex τ} → Operation (Φ := Φ) Γ i → Nat
  | _, .fv _ => 0
  | _, .bv _ => 0
  | _, .op _ => 1
  | _, .let₁ _ _ => 2
  | _, .unit => 0
  | _, .pair _ _ => 2
  | _, .let₂ _ _ _ => 2
  | _, .inl _ _ => 1
  | _, .inr _ _ => 1
  | _, .case _ _ _ => 3
  | _, .abort _ => 1
  | _, .sub _ => 1

/-- The source sort of every argument, including each binder's added types. -/
abbrev argSort : {i : TypingIndex τ} → (o : Operation (Φ := Φ) Γ i) → Fin o.arity → TypingIndex τ
  | _, .fv _, j => Fin.elim0 j
  | _, .bv _, j => Fin.elim0 j
  | _, .op (β := β) f, _ => ⟨_, β, instrSrc f⟩
  | _, .let₁ (β := β) A B, j => Fin.cases ⟨_, β, A⟩ (fun _ => ⟨_, β.snoc A, B⟩) j
  | _, .unit, j => Fin.elim0 j
  | _, .pair (β := β) A B, j => Fin.cases ⟨_, β, A⟩ (fun _ => ⟨_, β, B⟩) j
  | _, .let₂ (β := β) A B C, j =>
      Fin.cases ⟨_, β, product A B⟩ (fun _ => ⟨_, (β.snoc A).snoc B, C⟩) j
  | _, .inl (β := β) A _, _ => ⟨_, β, A⟩
  | _, .inr (β := β) _ B, _ => ⟨_, β, B⟩
  | _, .case (β := β) A B C, j =>
      Fin.cases ⟨_, β, coprod A B⟩
        (Fin.cases ⟨_, β.snoc A, C⟩ (fun _ => ⟨_, β.snoc B, C⟩)) j
  | _, .abort (β := β) _, _ => ⟨_, β, Silmaril.empty⟩
  | _, .sub (β := β) (A := A) _, _ => ⟨_, β, A⟩

end Operation

/-- The many-sorted signature includes every constructor of the calculus. -/
abbrev signature (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) : TheoryModel.Signature (TypingIndex τ) where
  Op := Operation (Φ := Φ) Γ
  arity := Operation.arity
  argSort := Operation.argSort

/-- A raw term with its exact typing derivation, including all subtype witnesses. -/
abbrev Carrier (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) := TypedTerm Φ Γ

variable {Γ : Ctx ν τ}

def syntaxOp : {i : TypingIndex τ} → (o : Operation (Φ := Φ) Γ i) →
    ((j : Fin o.arity) → Carrier Φ Γ (o.argSort j)) → Carrier Φ Γ i
  | _, .fv h, _ => ⟨.fv _, .fv h⟩
  | _, .bv i, _ => ⟨.bv i, .bv⟩
  | _, .op f, a => ⟨.op f (a 0).1, .op (a 0).2⟩
  | _, .let₁ _ _, a => ⟨.let₁ (a 0).1 (a 1).1, .let₁ (a 0).2 (a 1).2⟩
  | _, .unit, _ => ⟨.unit, .unit⟩
  | _, .pair _ _, a => ⟨.pair (a 0).1 (a 1).1, .pair (a 0).2 (a 1).2⟩
  | _, .let₂ _ _ _, a => ⟨.let₂ (a 0).1 (a 1).1, .let₂ (a 0).2 (a 1).2⟩
  | _, .inl _ _, a => ⟨.inl (a 0).1, .inl (a 0).2⟩
  | _, .inr _ _, a => ⟨.inr (a 0).1, .inr (a 0).2⟩
  | _, .case _ _ _, a => ⟨.case (a 0).1 (a 1).1 (a 2).1, .case (a 0).2 (a 1).2 (a 2).2⟩
  | _, .abort _, a => ⟨.abort (a 0).1, .abort (a 0).2⟩
  | _, .sub d, a => ⟨(a 0).1, .sub (a 0).2 d⟩

/-- The unquotiented exact syntax, as an algebra of all its constructors. -/
def syntaxAlgebra (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) : Algebra (signature Φ Γ) where
  Carrier := Carrier Φ Γ
  op := syntaxOp

/-- Interpret a data-valued exact derivation by the model operations. -/
def denote (X : Algebra (signature Φ Γ)) :
    {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
      HasType Φ Γ β t A → X.Carrier ⟨n, β, A⟩
  | _, _, _, _, .fv h => X.op (.fv h) (fun j => Fin.elim0 j)
  | _, _, _, _, .bv (ι := i) => X.op (.bv i) (fun j => Fin.elim0 j)
  | _, _, _, _, .op (f := f) ha => X.op (.op f) (fun _ => denote X ha)
  | _, _, _, _, .let₁ (A := A) (B := B) ha hb =>
      X.op (.let₁ A B) (Fin.cases (denote X ha) (fun _ => denote X hb))
  | _, _, _, _, .unit => X.op .unit (fun j => Fin.elim0 j)
  | _, _, _, _, .pair (A := A) (B := B) ha hb =>
      X.op (.pair A B) (Fin.cases (denote X ha) (fun _ => denote X hb))
  | _, _, _, _, .let₂ (A := A) (B := B) (C := C) ha hb =>
      X.op (.let₂ A B C) (Fin.cases (denote X ha) (fun _ => denote X hb))
  | _, _, _, _, .inl (A := A) (B := B) ha => X.op (.inl A B) (fun _ => denote X ha)
  | _, _, _, _, .inr (A := A) (B := B) hb => X.op (.inr A B) (fun _ => denote X hb)
  | _, _, _, _, .case (A := A) (B := B) (C := C) he hl hr =>
      X.op (.case A B C)
        (Fin.cases (denote X he) (Fin.cases (denote X hl) (fun _ => denote X hr)))
  | _, _, _, _, .abort (C := C) ha => X.op (.abort C) (fun _ => denote X ha)
  | _, _, _, _, .sub ha d => X.op (.sub d) (fun _ => denote X ha)

/-- The structural fold from exact syntax into an arbitrary operation algebra. -/
def fold (X : Algebra (signature Φ Γ)) : syntaxAlgebra Φ Γ ⟶ X where
  map a := denote X a.2
  comm o a := by
    cases o <;> dsimp only [syntaxAlgebra, syntaxOp, denote]
    all_goals congr 1; funext j; fin_cases j <;> rfl

/-- Every operation-preserving map agrees with structural interpretation. -/
theorem map_denote (X : Algebra (signature Φ Γ)) (F : syntaxAlgebra Φ Γ ⟶ X)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : HasType Φ Γ β t A) : F.map ⟨t, d⟩ = denote X d := by
  induction d with
  | @fv x A n β h =>
      exact (F.comm (.fv (β := β) h) (fun j => Fin.elim0 j)).trans
        (congrArg (X.op (.fv (β := β) h)) (funext fun j => Fin.elim0 j))
  | @bv n β i =>
      exact (F.comm (.bv (β := β) i) (fun j => Fin.elim0 j)).trans
        (congrArg (X.op (.bv (β := β) i)) (funext fun j => Fin.elim0 j))
  | @unit n β =>
      exact (F.comm (Operation.unit (β := β)) (fun j => Fin.elim0 j)).trans
        (congrArg (X.op (Operation.unit (β := β))) (funext fun j => Fin.elim0 j))
  | @op n β a f ha ih =>
      exact (F.comm (.op (β := β) f) (fun _ => ⟨a, ha⟩)).trans
        (congrArg (X.op (.op (β := β) f)) (funext fun _ => ih))
  | @let₁ n β a A b B ha hb iha ihb =>
      refine (F.comm (.let₁ (β := β) A B) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
      apply congrArg (X.op (.let₁ (β := β) A B))
      funext j
      fin_cases j <;> assumption
  | @pair n β a A b B ha hb iha ihb =>
      refine (F.comm (.pair (β := β) A B) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
      apply congrArg (X.op (.pair (β := β) A B))
      funext j
      fin_cases j <;> assumption
  | @let₂ n β a A B b C ha hb iha ihb =>
      refine (F.comm (.let₂ (β := β) A B C) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
      apply congrArg (X.op (.let₂ (β := β) A B C))
      funext j
      fin_cases j <;> assumption
  | @inl n β a A B ha ih =>
      exact (F.comm (.inl (β := β) A B) (fun _ => ⟨a, ha⟩)).trans
        (congrArg (X.op (.inl (β := β) A B)) (funext fun _ => ih))
  | @inr n β b B A hb ih =>
      exact (F.comm (.inr (β := β) A B) (fun _ => ⟨b, hb⟩)).trans
        (congrArg (X.op (.inr (β := β) A B)) (funext fun _ => ih))
  | @case n β e A B l C r he hl hr ihe ihl ihr =>
      refine (F.comm (.case (β := β) A B C)
        (Fin.cases ⟨e, he⟩ (Fin.cases ⟨l, hl⟩ (fun _ => ⟨r, hr⟩)))).trans ?_
      apply congrArg (X.op (.case (β := β) A B C))
      funext j
      fin_cases j <;> assumption
  | @abort n β a C ha ih =>
      exact (F.comm (.abort (β := β) C) (fun _ => ⟨a, ha⟩)).trans
        (congrArg (X.op (.abort (β := β) C)) (funext fun _ => ih))
  | @sub n β a A B ha d ih =>
      exact (F.comm (.sub (β := β) d) (fun _ => ⟨a, ha⟩)).trans
        (congrArg (X.op (.sub (β := β) d)) (funext fun _ => ih))

/-- Uniqueness of structural interpretation is a theorem about every homomorphism. -/
theorem fold_unique (X : Algebra (signature Φ Γ)) (F : syntaxAlgebra Φ Γ ⟶ X) :
    F = fold X := by
  apply Algebra.Hom.ext
  intro i a
  rcases i with ⟨n, β, A⟩
  rcases a with ⟨t, d⟩
  exact map_denote X F d

/-- Exact typing derivations form the initial algebra of constructor operations. -/
def syntaxIsInitial (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) :
    CategoryTheory.Limits.IsInitial (syntaxAlgebra Φ Γ) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom (fun X => fold X) (fun X F => fold_unique X F)

/-- Contextual compatibility gives operation compatibility at exact typing witnesses.
This bridge never erases the witnesses carried by terms or coercion operations. -/
def theoryPrecongruence (R : RefinementTheory (typedSyntax Φ Γ)) :
    CompatiblePreorder (syntaxAlgebra Φ Γ) where
  Rel := R.Rel
  refl := R.refl
  trans := R.trans
  compatible o a b h := by
    cases o with
    | fv hx => exact R.refl _
    | bv i => exact R.refl _
    | unit => exact R.refl _
    | op f => exact R.congr _ .op (h 0)
    | let₁ A B =>
      exact R.congr₂ _ (fun b => .let₁_left b) (fun a => .let₁_right a) (h 0) (h 1)
    | pair A B =>
      exact R.congr₂ _ (fun b => .pair_left b) (fun a => .pair_right a) (h 0) (h 1)
    | let₂ A B C =>
      exact R.congr₂ _ (fun b => .let₂_left b) (fun a => .let₂_right a) (h 0) (h 1)
    | inl A B => exact R.congr _ .inl (h 0)
    | inr A B => exact R.congr _ .inr (h 0)
    | case A B C =>
      exact R.congr₃ _ (fun l r => .case_scrutinee l r)
        (fun e r => .case_left e r) (fun e l => .case_right e l) (h 0) (h 1) (h 2)
    | abort C => exact R.congr _ .abort (h 0)
    | sub d => exact R.congr _ (.sub d) (h 0)

/-- A contextual equational theory gives a congruence on the same exact syntax. -/
def theoryCongruence (E : EquationalTheory (typedSyntax Φ Γ)) :
    Congruence (syntaxAlgebra Φ Γ) where
  Rel := E.Rel
  equivalence _ := ⟨E.refl, E.symm, E.trans⟩
  compatible := (theoryPrecongruence E.toRefinementTheory).compatible

variable {ε : Type r} [HasEff Φ ε]

/-- The typed equational congruence retains the exact endpoint witnesses. -/
def equationCongruence (pureEff : ε) (Γ : Ctx ν τ) : Congruence (syntaxAlgebra Φ Γ) :=
  theoryCongruence (equationalTheory pureEff Γ)

/-- Models need not interpret distinct subtype witnesses as the same operation. -/
abbrev EquationalModels (pureEff : ε) (Γ : Ctx ν τ) :=
  Silmaril.Logic.Metatheory.TheoryModel.Models (syntaxIsInitial Φ Γ) (equationCongruence pureEff Γ)

noncomputable def syntacticModel (pureEff : ε) (Γ : Ctx ν τ) :
    EquationalModels (Φ := Φ) pureEff Γ :=
  quotientModel (syntaxIsInitial Φ Γ) (equationCongruence pureEff Γ)

/-- The quotient by exact typed equations is initial among witness-preserving algebras. -/
noncomputable def syntacticModelIsInitial (pureEff : ε) (Γ : Ctx ν τ) :
    CategoryTheory.Limits.IsInitial (syntacticModel (Φ := Φ) pureEff Γ) :=
  quotientIsInitial (syntaxIsInitial Φ Γ) (equationCongruence pureEff Γ)

/-- Equality valid in every witness-preserving model is precisely typed equality. -/
theorem semantic_iff (pureEff : ε) (Γ : Ctx ν τ) {i : TypingIndex τ}
    (a b : Carrier Φ Γ i) : TypedEquiv.Related pureEff Γ a.2 b.2 ↔
      ∀ M : EquationalModels (Φ := Φ) pureEff Γ,
        ((syntaxIsInitial Φ Γ).to M.algebra).map a = ((syntaxIsInitial Φ Γ).to M.algebra).map b :=
  Silmaril.Logic.Metatheory.TheoryModel.semantic_iff
    (syntaxIsInitial Φ Γ) (equationCongruence pureEff Γ) a b

/-- Generated exact-witness refinement is compatible with every constructor. -/
def refinementPreorder (pureEff : ε) (Γ : Ctx ν τ) (R : Refinement.Theory (Φ := Φ) Γ) :
    CompatiblePreorder (syntaxAlgebra Φ Γ) :=
  theoryPrecongruence (refinementTheory pureEff Γ R)

/-- Ordered witness-preserving models of an arbitrary primitive rewrite theory. -/
abbrev RefinementModels (pureEff : ε) (Γ : Ctx ν τ) (R : Refinement.Theory (Φ := Φ) Γ) :=
  OrderedModels (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

noncomputable def orderedSyntacticModel (pureEff : ε) (Γ : Ctx ν τ)
    (R : Refinement.Theory (Φ := Φ) Γ) : RefinementModels pureEff Γ R :=
  orderedQuotientModel (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- The antisymmetrized exact-witness syntax is an initial ordered algebra. -/
noncomputable def orderedSyntacticModelIsInitial (pureEff : ε) (Γ : Ctx ν τ)
    (R : Refinement.Theory (Φ := Φ) Γ) :
    CategoryTheory.Limits.IsInitial (orderedSyntacticModel pureEff Γ R) :=
  orderedQuotientIsInitial (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- The model order records exactly derivable refinement at these witnesses. -/
theorem orderedSyntacticModel_le_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : Refinement.Theory (Φ := Φ) Γ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (show (orderedSyntacticModel pureEff Γ R).algebra.Carrier i from
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map a) ≤
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map b ↔
      Refinement.Related pureEff Γ R a.2 b.2 := Iff.rfl

/-- Semantic soundness and completeness quantify over all ordered operation models. -/
theorem refinement_iff_all_models (pureEff : ε) (Γ : Ctx ν τ)
    (R : Refinement.Theory (Φ := Φ) Γ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    SemanticallyRefines (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b ↔
      Refinement.Related pureEff Γ R a.2 b.2 :=
  semanticallyRefines_iff (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b

/-- No equality of typing or subtyping derivations is needed for model completeness. -/
theorem mutual_refinement_iff_all_models (pureEff : ε) (Γ : Ctx ν τ)
    (R : Refinement.Theory (Φ := Φ) Γ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (∀ M : RefinementModels pureEff Γ R,
      ((syntaxIsInitial Φ Γ).to M.algebra.toAlgebra).map a =
        ((syntaxIsInitial Φ Γ).to M.algebra.toAlgebra).map b) ↔
      Refinement.Equivalent pureEff Γ R a.2 b.2 :=
  semanticallyEqual_iff (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b

end Silmaril.Isotope.LetCase.ProofRelevant.LocallyNameless.Models
