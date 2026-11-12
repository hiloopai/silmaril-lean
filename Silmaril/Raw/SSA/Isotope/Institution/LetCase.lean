module

public import Silmaril.Raw.SSA.Isotope.Institution.Presented
public import Silmaril.Raw.SSA.Isotope.Institution.InstrSig
public import Silmaril.Raw.SSA.Isotope.Institution.LetCaseSig
public import Silmaril.Raw.SSA.Isotope.Theory.Models.Theories
public import Silmaril.Raw.SSA.Isotope.Morphism.Instructions.LetCase

@[expose] public section

/-!
# The equational institution of exactly typed LetCase

Fix a type universe `τ`, effects `ε`, variable names `ν` and a free-variable context
`Γ : Ctx ν τ`. The institution `LetCase.inst Γ : InstrSig τ ε ⥤ Room` has

* signatures: primitive instruction signatures `P` with instruction relabellings;
* sentences over `P`: typed equations `β ⊢ a = b : A` in context `Γ`, between exactly typed
  locally nameless terms with data-valued derivations (the carriers of
  `LetCase.LocallyNameless.Models.syntaxAlgebra`);
* models over `P`: all operation algebras of `LetCase.LocallyNameless.Models.signature P Γ`;
* satisfaction: the structural denotation `Models.denote` identifies the two sides;
* reduct along `g`: the existing `TheoryModel.Algebra.reduct` along the operation map `sigHom`.

It is the composite of the functor `pres Γ : InstrSig τ ε ⥤ PresSig` with the institution of
presented syntax `PresSig.inst`, so its satisfaction condition is `TheoryModel.reindex_fold_map`.

The base equational theory and every equational extension of it give theories of the
institution (`baseTheory`, `theoryFunctor`). Their entailment is derivability
(`entails_base_iff`, from `Models.semantic_iff`; `entails_theory_iff`, from
`Models.theory_semantic_iff`), and their institution model categories are the existing
`Models.EquationalModels` and `Models.ModelsOfTheory` (`modelsEquivalence`).
-/

namespace Silmaril.Isotope.Institution.LetCase

open CategoryTheory
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory
open Silmaril.Isotope.Theory
open Silmaril.Isotope.LetCase.LocallyNameless

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν] (Γ : Ctx ν τ)

/-- Exact LetCase syntax in context `Γ`, as a presented syntax. -/
def presObj (P : InstrSig τ ε) : PresSig.{u, u, u} where
  Idx := TypingIndex τ
  Sig := Models.signature P.Instr Γ
  Syn := Models.syntaxAlgebra P.Instr Γ
  isInitial := Models.syntaxIsInitial P.Instr Γ

/-- Instruction signatures to presented LetCase syntax. -/
def pres : InstrSig τ ε ⥤ PresSig.{u, u, u} where
  obj := presObj Γ
  map g := sigHom Γ g
  map_id P := sigHom_id Γ P
  map_comp f g := sigHom_comp Γ f g

/-- The equational institution of exactly typed LetCase in context `Γ`. -/
def inst : InstrSig τ ε ⥤ Silmaril.Logic.Institution.Room.{u, u, u + 1} :=
  pres Γ ⋙ PresSig.inst

/-! ### Satisfaction -/

/-- Satisfaction is equality of structural denotations. -/
theorem sat_iff (P : InstrSig τ ε) (M : TheoryModel.Algebra.{u, u, u} (Models.signature P.Instr Γ))
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν P.Instr n} {A : τ}
    (da : Derivation P.Instr Γ β a A) (db : Derivation P.Instr Γ β b A) :
    ((inst (ε := ε) Γ).obj P).Sat M ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ ↔
      Models.denote M da = Models.denote M db := by
  change ((Models.syntaxIsInitial P.Instr Γ).to M).map (i := ⟨n, β, A⟩) ⟨a, da⟩ =
      ((Models.syntaxIsInitial P.Instr Γ).to M).map (i := ⟨n, β, A⟩) ⟨b, db⟩ ↔ _
  rw [Models.syntaxIsInitial_to]
  rfl

/-- The satisfaction condition of the LetCase institution, read off the room functor. -/
theorem satisfaction {P Q : InstrSig τ ε} (g : P ⟶ Q)
    (M : ((inst (ε := ε) Γ).obj Q).Mod) (e : ((inst (ε := ε) Γ).obj P).Sen) :
    ((inst (ε := ε) Γ).obj Q).Sat M (((inst (ε := ε) Γ).map g).sen e) ↔
      ((inst (ε := ε) Γ).obj P).Sat ((((inst (ε := ε) Γ).map g)).mod.obj M) e :=
  Silmaril.Logic.Institution.satisfaction_condition (inst (ε := ε) Γ) g M e

/-- The operation `castOp (op q)` of the target syntax builds the term `op q`. -/
theorem syntaxOp_castOp_op_fst {Q : InstrSig τ ε} {n : Nat} {β : BoundCtx τ n} {A S : τ}
    (q : Q.Instr) (hA : instrTrg q = A) (hS : instrSrc q = S)
    (args : (j : Fin ((Models.signature Q.Instr Γ).arity
        (castOp (Models.signature Q.Instr Γ)
          (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) hA) (Models.Operation.op (β := β) q)))) →
      Models.Carrier Q.Instr Γ ((Models.signature Q.Instr Γ).argSort
        (castOp (Models.signature Q.Instr Γ)
          (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) hA) (Models.Operation.op (β := β) q)) j))
    (x : Models.Carrier Q.Instr Γ ⟨n, β, S⟩) (hx : ∀ j, HEq (args j) x) :
    (Models.syntaxOp (castOp (Models.signature Q.Instr Γ)
        (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) hA)
        (Models.Operation.op (β := β) q)) args).1 = Tm.op q x.1 := by
  subst hA
  subst hS
  have h : args = fun _ => x := funext fun j => eq_of_heq (hx j)
  subst h
  rfl

/-- Folding a derivation into the reduct of the target syntax relabels its term. -/
theorem denote_reduct_fst {P Q : InstrSig τ ε} (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν P.Instr n} {A : τ} (d : Derivation P.Instr Γ β t A) :
    (Models.denote (TheoryModel.Algebra.reductObj (sigHom Γ g) (Models.syntaxAlgebra Q.Instr Γ))
      d : Models.Carrier Q.Instr Γ ⟨n, β, A⟩).1 = Tm.mapInstr (InstrSig.Hom.instr g) t := by
  induction d with
  | fv h => rfl
  | bv => rfl
  | unit => rfl
  | @op n β f a ha ih =>
      rw [Tm.mapInstr_op, ← ih]
      exact syntaxOp_castOp_op_fst Γ (g.instr f) (g.target f) (g.source f) _ _
        (fun _ => eqRec_heq _ _)
  | let₁ ha hb iha ihb =>
      rw [Tm.mapInstr_let₁, ← iha, ← ihb]
      rfl
  | pair ha hb iha ihb =>
      rw [Tm.mapInstr_pair, ← iha, ← ihb]
      rfl
  | let₂ ha hb iha ihb =>
      rw [Tm.mapInstr_let₂, ← iha, ← ihb]
      rfl
  | inl ha ih =>
      rw [Tm.mapInstr_inl, ← ih]
      rfl
  | inr hb ih =>
      rw [Tm.mapInstr_inr, ← ih]
      rfl
  | case he hl hr ihe ihl ihr =>
      rw [Tm.mapInstr_case, ← ihe, ← ihl, ← ihr]
      rfl
  | abort ha ih =>
      rw [Tm.mapInstr_abort, ← ih]
      rfl

/-- The term component of a translated sentence is the existing instruction relabelling. -/
theorem translate_fst {P Q : InstrSig τ ε} (g : P ⟶ Q) {i : TypingIndex τ}
    (x : Models.Carrier P.Instr Γ i) :
    ((PresSig.translate ((pres (ε := ε) Γ).map g)).map x).1 = Tm.mapInstr (InstrSig.Hom.instr g) x.1 := by
  obtain ⟨n, β, A⟩ := i
  obtain ⟨t, d⟩ := x
  -- The translation is the structural fold (`Models.syntaxIsInitial_to`), definitionally.
  exact denote_reduct_fst Γ g d

/-! ### Theories -/

variable {Γ}

/-- The sentences of the base exact equational theory of LetCase. -/
abbrev baseSentences (pureEff : ε) (P : InstrSig τ ε) : Set ((inst (ε := ε) Γ).obj P).Sen :=
  PresSig.equations (X := (pres (ε := ε) Γ).obj P) (Models.equationCongruence pureEff Γ)

/-- Semantic consequence from the base theory is exact derivability. This is the institution
form of completeness of the quotient model (`PresSig.entails_equations_iff`, from
`TheoryModel.semantic_iff`); see `entails_base_iff_denote` for the form of
`LetCase.LocallyNameless.Models.semantic_iff`. -/
theorem entails_base_iff (pureEff : ε) (P : InstrSig τ ε)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν P.Instr n} {A : τ}
    (da : Derivation P.Instr Γ β a A) (db : Derivation P.Instr Γ β b A) :
    ((inst (ε := ε) Γ).obj P).Entails (baseSentences pureEff P) ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ ↔
      Silmaril.Isotope.LetCase.LocallyNameless.Equiv pureEff Γ β a b A :=
  PresSig.entails_equations_iff (X := (pres (ε := ε) Γ).obj P)
    (Models.equationCongruence pureEff Γ) ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩

/-- Semantic consequence from the base theory is equality of denotations in every existing
equational model: `entails_base_iff` composed with `LetCase.LocallyNameless.Models.semantic_iff`. -/
theorem entails_base_iff_denote (pureEff : ε) (P : InstrSig τ ε)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν P.Instr n} {A : τ}
    (da : Derivation P.Instr Γ β a A) (db : Derivation P.Instr Γ β b A) :
    ((inst (ε := ε) Γ).obj P).Entails (baseSentences pureEff P) ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ ↔
      ∀ M : Models.EquationalModels (Φ := P.Instr) pureEff Γ,
        Models.denote M.algebra da = Models.denote M.algebra db :=
  (entails_base_iff pureEff P da db).trans (Models.semantic_iff da db)

/-- Semantic consequence from any equational theory is membership in it
(`PresSig.entails_equations_iff`); see `entails_theory_iff_denote` for the form of
`LetCase.LocallyNameless.Models.theory_semantic_iff`. -/
theorem entails_theory_iff (P : InstrSig τ ε) (E : EquationalTheory (typedSyntax P.Instr Γ))
    {i : TypingIndex τ} (x y : Models.Carrier P.Instr Γ i) :
    ((inst (ε := ε) Γ).obj P).Entails
        (PresSig.equations (X := (pres (ε := ε) Γ).obj P) (Models.theoryCongruence E)) ⟨i, x, y⟩ ↔
      E.Rel (Models.eraseCarrier x) (Models.eraseCarrier y) :=
  PresSig.entails_equations_iff (X := (pres (ε := ε) Γ).obj P) (Models.theoryCongruence E)
    ⟨i, x, y⟩

/-- `entails_theory_iff` composed with `LetCase.LocallyNameless.Models.theory_semantic_iff`. -/
theorem entails_theory_iff_denote (P : InstrSig τ ε) (E : EquationalTheory (typedSyntax P.Instr Γ))
    {i : TypingIndex τ} (x y : Models.Carrier P.Instr Γ i) :
    ((inst (ε := ε) Γ).obj P).Entails
        (PresSig.equations (X := (pres (ε := ε) Γ).obj P) (Models.theoryCongruence E)) ⟨i, x, y⟩ ↔
      ∀ M : Models.ModelsOfTheory E, Models.denote M.algebra x.2 = Models.denote M.algebra y.2 :=
  (entails_theory_iff P E x y).trans (Models.theory_semantic_iff E x y)

/-- The theory of an exact equational theory over instruction signature `P`. -/
def theoryOf (P : InstrSig τ ε) (E : EquationalTheory (typedSyntax P.Instr Γ)) :
    Silmaril.Logic.Institution.Theory (inst (ε := ε) Γ) :=
  PresSig.theoryAt (pres (ε := ε) Γ) P (Models.theoryCongruence E)

/-- The base equational theory of LetCase, as a theory of the institution. -/
def baseTheory (pureEff : ε) (P : InstrSig τ ε) : Silmaril.Logic.Institution.Theory (inst (ε := ε) Γ) :=
  theoryOf P (equationalTheory pureEff Γ)

/-- The base theory's sentences are those of `Models.equationCongruence`
(`Models.theoryCongruence_base`). -/
theorem baseTheory_sentences (pureEff : ε) (P : InstrSig τ ε) :
    (baseTheory pureEff P).sentences = baseSentences (Γ := Γ) pureEff P := by
  simp only [baseTheory, theoryOf, PresSig.theoryAt, Models.theoryCongruence_base]

/-- Instruction maps are theory morphisms of the base theories, by
`LetCase.LocallyNameless.Equiv.mapInstr`. -/
def baseTheoryHom (pureEff : ε) {P Q : InstrSig τ ε} (g : P ⟶ Q) :
    baseTheory (Γ := Γ) pureEff P ⟶ baseTheory pureEff Q :=
  PresSig.theoryAtHom (pres (ε := ε) Γ) g (fun {i} {x y} h => by
    -- `LetCase.LocallyNameless.Equiv.mapInstr` along `g.toSignatureMap`, with `translate_fst`
    -- identifying the translated terms.
    have e := Silmaril.Isotope.LetCase.LocallyNameless.Equiv.mapInstr
      (InstrSig.Hom.toSignatureMap g) (show Silmaril.Isotope.LetCase.LocallyNameless.Equiv
        pureEff Γ i.bound x.1 y.1 i.result from h)
    change Silmaril.Isotope.LetCase.LocallyNameless.Equiv pureEff Γ i.bound
      ((PresSig.translate ((pres (ε := ε) Γ).map g)).map x).1
      ((PresSig.translate ((pres (ε := ε) Γ).map g)).map y).1 i.result
    rw [translate_fst Γ g x, translate_fst Γ g y]
    have e' : Silmaril.Isotope.LetCase.LocallyNameless.Equiv pureEff (Γ.mapTypes id)
        (i.bound.mapTypes id) (Tm.mapInstr (InstrSig.Hom.instr g) x.1)
        (Tm.mapInstr (InstrSig.Hom.instr g) y.1) i.result := e
    rw [Silmaril.Isotope.Ctx.mapTypes_id, Silmaril.Isotope.BoundCtx.mapTypes_id] at e'
    exact e')

/-- The base theories, as a functor from instruction signatures to `Th(LetCase.inst Γ)`. -/
def baseTheoryFunctor (pureEff : ε) :
    InstrSig τ ε ⥤ Silmaril.Logic.Institution.Theory (inst (ε := ε) Γ) where
  obj := baseTheory pureEff
  map g := baseTheoryHom pureEff g
  map_id _ := Silmaril.Logic.Institution.Theory.hom_ext rfl
  map_comp _ _ := Silmaril.Logic.Institution.Theory.hom_ext rfl

/-- The base theory functor lies over the identity of signatures. -/
theorem baseTheoryFunctor_comp_forget (pureEff : ε) :
    baseTheoryFunctor (Γ := Γ) pureEff ⋙ Silmaril.Logic.Institution.Theory.forget (inst (ε := ε) Γ) =
      𝟭 _ :=
  rfl

/-! ### Equational theories as institution theories -/

/-- An inclusion of equational theories is a theory morphism over the identity signature
morphism. -/
def theoryOfHom (P : InstrSig τ ε) {E E' : EquationalTheory (typedSyntax P.Instr Γ)}
    (h : E ≤ E') : theoryOf P E ⟶ theoryOf P E' :=
  Silmaril.Logic.Institution.Theory.homMk (𝟙 P) (fun e he =>
    (congrArg (fun c => Silmaril.Logic.Institution.Corridor.sen c e ∈ (theoryOf P E').sentences)
      ((inst (ε := ε) Γ).map_id P)).mpr (h he))

/-- Exact equational theories over `P` (ordered by inclusion), as theories of the institution.
This is the institution counterpart of `TypedEquationalTheories` and
`TypedEquationalExtensions`. -/
def theoryFunctor (P : InstrSig τ ε) :
    EquationalTheory (typedSyntax P.Instr Γ) ⥤ Silmaril.Logic.Institution.Theory (inst (ε := ε) Γ) where
  obj := theoryOf P
  map h := theoryOfHom P (leOfHom h)
  map_id _ := Silmaril.Logic.Institution.Theory.hom_ext rfl
  map_comp _ _ := Silmaril.Logic.Institution.Theory.hom_ext rfl

instance (P : InstrSig τ ε) : (theoryFunctor (Γ := Γ) P).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The sentence set of an equational theory determines it. -/
theorem theoryOf_sentences_subset_iff (P : InstrSig τ ε)
    (E E' : EquationalTheory (typedSyntax P.Instr Γ)) :
    (theoryOf (Γ := Γ) P E).sentences ⊆ (theoryOf P E').sentences ↔ E ≤ E' := by
  constructor
  · intro h i a b hab
    obtain ⟨a', rfl⟩ := Models.eraseCarrier_surjective (Φ := P.Instr) (Γ := Γ) i a
    obtain ⟨b', rfl⟩ := Models.eraseCarrier_surjective (Φ := P.Instr) (Γ := Γ) i b
    exact h (a := (⟨i, a', b'⟩ : ((inst (ε := ε) Γ).obj P).Sen)) hab
  · intro h e he
    exact h he

/-- The theory functor is full onto the theory morphisms over the identity signature morphism:
such a morphism comes from an inclusion of equational theories. -/
theorem theoryFunctor_full_over_id (P : InstrSig τ ε)
    {E E' : EquationalTheory (typedSyntax P.Instr Γ)}
    (f : (theoryFunctor (Γ := Γ) P).obj E ⟶ (theoryFunctor P).obj E')
    (hf : f.hom.sig = 𝟙 P) : ∃ h : E ⟶ E', (theoryFunctor P).map h = f := by
  obtain ⟨⟨σ, hσ⟩⟩ := f
  change σ = 𝟙 P at hf
  subst hf
  have hsub : (theoryOf (Γ := Γ) P E).sentences ⊆ (theoryOf P E').sentences := by
    intro e he
    exact (congrArg (fun c => Silmaril.Logic.Institution.Corridor.sen c e ∈ (theoryOf P E').sentences)
      ((inst (ε := ε) Γ).map_id P)).mp (hσ he)
  have hle : E ≤ E' := by
    intro i a b hab
    exact (theoryOf_sentences_subset_iff P E E').1 hsub hab
  exact ⟨homOfLE hle, Silmaril.Logic.Institution.Theory.hom_ext rfl⟩

/-- The theory functor is injective on objects. -/
theorem theoryFunctor_obj_injective (P : InstrSig τ ε) :
    Function.Injective (theoryFunctor (Γ := Γ) P).obj := by
  intro E E' h
  have h2 : (theoryOf (Γ := Γ) P E).sentences = (theoryOf P E').sentences :=
    eq_of_heq (congr_arg_heq
      (fun T : Silmaril.Logic.Institution.Theory (inst (ε := ε) Γ) => T.sentences) h)
  apply le_antisymm
  · intro i a b hab
    exact (theoryOf_sentences_subset_iff P E E').1 h2.subset hab
  · intro i a b hab
    exact (theoryOf_sentences_subset_iff P E' E).1 h2.symm.subset hab

/-- The existing models of an equational theory (`Models.ModelsOfTheory`) are the institution's
models of the corresponding theory. -/
def modelsEquivalence (P : InstrSig τ ε) (E : EquationalTheory (typedSyntax P.Instr Γ)) :
    Models.ModelsOfTheory E ≌ Silmaril.Logic.Institution.Theory.Models (theoryOf P E) :=
  PresSig.modelsEquivalence (pres (ε := ε) Γ) P (Models.theoryCongruence E)

/-- The existing models of the base theory (`Models.EquationalModels`) are the institution's
models of the base theory. -/
def baseModelsEquivalence (pureEff : ε) (P : InstrSig τ ε) :
    Models.EquationalModels (Φ := P.Instr) pureEff Γ ≌
      Silmaril.Logic.Institution.Theory.Models (baseTheory (Γ := Γ) pureEff P) :=
  modelsEquivalence P (equationalTheory pureEff Γ)

end Silmaril.Isotope.Institution.LetCase
