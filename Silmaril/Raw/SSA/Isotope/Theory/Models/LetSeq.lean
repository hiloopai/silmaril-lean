module

public import Silmaril.Logic.Metatheory.Theory.Model
public import Silmaril.Raw.SSA.Isotope.Theory.Contexts
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Derivation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-!
# Operation algebras and the exact syntactic model of LetSeq

Every constructor acts as an operation, with binder bodies placed at their
extended context sorts. The free operation algebra uses data-valued exact
typing derivations. Quotienting by exact equations also identifies different
derivations of the same typed term, so model interpretation is coherent.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.LetSeq.LocallyNameless.Models

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory

variable {τ : Type u} [HasProduct τ] [HasUnit τ] {ν : Type w} [DecidableEq ν]
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

end Operation

/-- The many-sorted signature includes every constructor of the calculus. -/
abbrev signature (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) : Silmaril.Logic.Metatheory.TheoryModel.Signature (TypingIndex τ) where
  Op := Operation (Φ := Φ) Γ
  arity := Operation.arity
  argSort := Operation.argSort

/-- Typing derivations are data; no elimination from `HasType : Prop` is needed. -/
def Carrier (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  (t : Tm ν Φ i.depth) × Derivation Φ Γ i.bound t i.result

variable {Γ : Ctx ν τ}

/-- Forget data-valued typing evidence, retaining exact propositional typing. -/
def eraseCarrier {i : TypingIndex τ} (a : Carrier Φ Γ i) : TypedTerm Φ Γ i :=
  ⟨a.1, a.2.toHasType⟩

/-- Every exactly typed term has a representative in the free derivation algebra. -/
theorem eraseCarrier_surjective (i : TypingIndex τ) :
    Function.Surjective (eraseCarrier (Φ := Φ) (Γ := Γ) (i := i)) := by
  intro a
  obtain ⟨d⟩ := Derivation.ofHasType a.property
  exact ⟨⟨a.val, d⟩, rfl⟩

def syntaxOp : {i : TypingIndex τ} → (o : Operation (Φ := Φ) Γ i) →
    ((j : Fin o.arity) → Carrier Φ Γ (o.argSort j)) → Carrier Φ Γ i
  | _, .fv h, _ => ⟨.fv _, .fv h⟩
  | _, .bv i, _ => ⟨.bv i, .bv⟩
  | _, .op f, a => ⟨.op f (a 0).1, .op (a 0).2⟩
  | _, .let₁ _ _, a => ⟨.let₁ (a 0).1 (a 1).1, .let₁ (a 0).2 (a 1).2⟩
  | _, .unit, _ => ⟨.unit, .unit⟩
  | _, .pair _ _, a => ⟨.pair (a 0).1 (a 1).1, .pair (a 0).2 (a 1).2⟩
  | _, .let₂ _ _ _, a => ⟨.let₂ (a 0).1 (a 1).1, .let₂ (a 0).2 (a 1).2⟩

/-- The unquotiented exact syntax, as an algebra of all its constructors. -/
def syntaxAlgebra (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) : Algebra (signature Φ Γ) where
  Carrier := Carrier Φ Γ
  op := syntaxOp

/-- Interpret a data-valued exact derivation by the model operations. -/
def denote (X : Algebra (signature Φ Γ)) :
    {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
      Derivation Φ Γ β t A → X.Carrier ⟨n, β, A⟩
  | _, _, _, _, .fv h => X.op (.fv h) (fun j => Fin.elim0 j)
  | _, _, _, _, .bv (i := i) => X.op (.bv i) (fun j => Fin.elim0 j)
  | _, _, _, _, .op (f := f) ha => X.op (.op f) (fun _ => denote X ha)
  | _, _, _, _, .let₁ (A := A) (B := B) ha hb =>
      X.op (.let₁ A B) (Fin.cases (denote X ha) (fun _ => denote X hb))
  | _, _, _, _, .unit => X.op .unit (fun j => Fin.elim0 j)
  | _, _, _, _, .pair (A := A) (B := B) ha hb =>
      X.op (.pair A B) (Fin.cases (denote X ha) (fun _ => denote X hb))
  | _, _, _, _, .let₂ (A := A) (B := B) (C := C) ha hb =>
      X.op (.let₂ A B C) (Fin.cases (denote X ha) (fun _ => denote X hb))

/-- The structural fold from exact syntax into an arbitrary operation algebra. -/
def fold (X : Algebra (signature Φ Γ)) : syntaxAlgebra Φ Γ ⟶ X where
  map a := denote X a.2
  comm o a := by
    cases o <;> dsimp only [syntaxAlgebra, syntaxOp, denote]
    all_goals congr 1; funext j; fin_cases j <;> rfl

/-- Every operation-preserving map agrees with structural interpretation. -/
theorem map_denote (X : Algebra (signature Φ Γ)) (F : syntaxAlgebra Φ Γ ⟶ X)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) : F.map ⟨t, d⟩ = denote X d := by
  induction d with
  | @fv n β x A h =>
      exact (F.comm (.fv (β := β) h) (fun j => Fin.elim0 j)).trans
        (congrArg (X.op (.fv (β := β) h)) (funext fun j => Fin.elim0 j))
  | @bv n β i =>
      exact (F.comm (.bv (β := β) i) (fun j => Fin.elim0 j)).trans
        (congrArg (X.op (.bv (β := β) i)) (funext fun j => Fin.elim0 j))
  | @unit n β =>
      exact (F.comm (Operation.unit (β := β)) (fun j => Fin.elim0 j)).trans
        (congrArg (X.op (Operation.unit (β := β))) (funext fun j => Fin.elim0 j))
  | @op n β f a ha ih =>
      exact (F.comm (.op (β := β) f) (fun _ => ⟨a, ha⟩)).trans
        (congrArg (X.op (.op (β := β) f)) (funext fun _ => ih))
  | @let₁ n β a b A B ha hb iha ihb =>
      refine (F.comm (.let₁ (β := β) A B) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
      apply congrArg (X.op (.let₁ (β := β) A B))
      funext j
      fin_cases j <;> assumption
  | @pair n β a b A B ha hb iha ihb =>
      refine (F.comm (.pair (β := β) A B) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
      apply congrArg (X.op (.pair (β := β) A B))
      funext j
      fin_cases j <;> assumption
  | @let₂ n β a b A B C ha hb iha ihb =>
      refine (F.comm (.let₂ (β := β) A B C) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
      apply congrArg (X.op (.let₂ (β := β) A B C))
      funext j
      fin_cases j <;> assumption

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

/-- The initial map computes as the structural fold. -/
@[simp] theorem syntaxIsInitial_to (X : Algebra (signature Φ Γ)) :
    (syntaxIsInitial Φ Γ).to X = fold X :=
  fold_unique X ((syntaxIsInitial Φ Γ).to X)

variable {ε : Type r} [HasEff Φ ε]

/-- Exact equations are compatible with every operation of the syntax algebra. -/
def equationCongruence (pureEff : ε) (Γ : Ctx ν τ) : Congruence (syntaxAlgebra Φ Γ) where
  Rel {i} a b := Equiv pureEff Γ i.bound a.1 b.1 i.result
  equivalence _ := ⟨fun a => .refl a.2.toHasType, Equiv.symm, Equiv.trans⟩
  compatible o a b h := by
    cases o with
    | fv hx => exact .refl (.fv hx)
    | bv i => exact .refl .bv
    | unit => exact .unit
    | op f => exact .op (h 0)
    | let₁ A B => exact .let₁ (h 0) (h 1)
    | pair A B => exact .pair (h 0) (h 1)
    | let₂ A B C => exact .let₂ (h 0) (h 1)

/-- Algebras of the exact equational presentation, with constructor-preserving maps. -/
abbrev EquationalModels (pureEff : ε) (Γ : Ctx ν τ) :=
  Silmaril.Logic.Metatheory.TheoryModel.Models (syntaxIsInitial Φ Γ) (equationCongruence pureEff Γ)

/-- Exact typed syntax modulo equations, as a model with all constructor operations. -/
noncomputable def syntacticModel (pureEff : ε) (Γ : Ctx ν τ) :
    EquationalModels (Φ := Φ) pureEff Γ :=
  quotientModel (syntaxIsInitial Φ Γ) (equationCongruence pureEff Γ)

/-- The interpretation into every model exists and is the unique operation homomorphism. -/
noncomputable def syntacticModelIsInitial (pureEff : ε) (Γ : Ctx ν τ) :
    CategoryTheory.Limits.IsInitial (syntacticModel (Φ := Φ) pureEff Γ) :=
  quotientIsInitial (syntaxIsInitial Φ Γ) (equationCongruence pureEff Γ)

/-- Equation validity in every operation algebra is exactly derivability. -/
theorem semantic_iff {pureEff : ε} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    Equiv pureEff Γ β a b A ↔
      ∀ M : EquationalModels (Φ := Φ) pureEff Γ,
        denote M.algebra da = denote M.algebra db := by
  simpa only [syntaxIsInitial_to, fold, equationCongruence, EquationalModels] using
    (Silmaril.Logic.Metatheory.TheoryModel.semantic_iff
      (syntaxIsInitial Φ Γ) (equationCongruence pureEff Γ) (i := ⟨n, β, A⟩) ⟨a, da⟩ ⟨b, db⟩)

/-- A model's denotation depends on the typed term, not the chosen derivation. -/
theorem denote_coherent {pureEff : ε} (M : EquationalModels (Φ := Φ) pureEff Γ)
    {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
    (d e : Derivation Φ Γ β a A) : denote M.algebra d = denote M.algebra e :=
  (semantic_iff d e).1 (.refl d.toHasType) M

/-- Interpret propositionally typed syntax using any exact derivation. -/
noncomputable def interpret {pureEff : ε} (M : EquationalModels (Φ := Φ) pureEff Γ)
    {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β a A) : M.algebra.Carrier ⟨n, β, A⟩ :=
  denote M.algebra (Classical.choice (Derivation.ofHasType h))

@[simp] theorem interpret_derivation {pureEff : ε} (M : EquationalModels (Φ := Φ) pureEff Γ)
    {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β a A) : interpret M d.toHasType = denote M.algebra d :=
  denote_coherent M _ d

/-- Soundness and completeness stated directly for propositionally typed terms. -/
theorem interpret_eq_iff {pureEff : ε} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ} (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    Equiv pureEff Γ β a b A ↔
      ∀ M : EquationalModels (Φ := Φ) pureEff Γ, interpret M ha = interpret M hb :=
  semantic_iff (Classical.choice (Derivation.ofHasType ha))
    (Classical.choice (Derivation.ofHasType hb))

/-- The same quotient described using raw terms with proposition-valued typing evidence. -/
def typedTermSetoid (pureEff : ε) (Γ : Ctx ν τ) (i : TypingIndex τ) :
    Setoid (TypedTerm Φ Γ i) where
  r a b := Equiv pureEff Γ i.bound a.val b.val i.result
  iseqv := ⟨fun a => .refl a.property, Equiv.symm, Equiv.trans⟩

abbrev TermQuotient (pureEff : ε) (Γ : Ctx ν τ) (i : TypingIndex τ) :=
  Quotient (typedTermSetoid (Φ := Φ) pureEff Γ i)

/-- The initial model carrier is exactly the quotient of typable raw syntax;
the derivation data used to construct its operations leaves no extra distinction. -/
noncomputable def syntaxQuotientEquiv (pureEff : ε) (Γ : Ctx ν τ) (i : TypingIndex τ) :
    (syntacticModel (Φ := Φ) pureEff Γ).algebra.Carrier i ≃ TermQuotient (Φ := Φ) pureEff Γ i :=
  quotientEquivOfSurjective ((equationCongruence (Φ := Φ) pureEff Γ).setoid i)
    (typedTermSetoid pureEff Γ i) eraseCarrier (eraseCarrier_surjective i) (fun _ _ => Iff.rfl)

/-- The carrier equivalence erases a representative's derivation evidence. -/
@[simp] theorem syntaxQuotientEquiv_mk (pureEff : ε) (Γ : Ctx ν τ)
    (i : TypingIndex τ) (a : Carrier Φ Γ i) :
    syntaxQuotientEquiv pureEff Γ i ((quotientMap (equationCongruence pureEff Γ)).map a) =
      Quotient.mk _ (eraseCarrier a) := rfl

/-- The quotient map is exact: it identifies precisely the provable equations. -/
theorem quotient_eq_iff {pureEff : ε} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A : τ} (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    (quotientMap (equationCongruence (Φ := Φ) pureEff Γ)).map (i := ⟨n, β, A⟩) ⟨a, da⟩ =
      (quotientMap (equationCongruence (Φ := Φ) pureEff Γ)).map (i := ⟨n, β, A⟩) ⟨b, db⟩ ↔
        Equiv pureEff Γ β a b A :=
  quotientMap_eq_iff (equationCongruence pureEff Γ) (i := ⟨n, β, A⟩) ⟨a, da⟩ ⟨b, db⟩

end Silmaril.Isotope.LetSeq.LocallyNameless.Models
