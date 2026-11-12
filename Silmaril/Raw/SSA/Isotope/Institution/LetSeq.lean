module

public import Silmaril.Raw.SSA.Isotope.Institution.Presented
public import Silmaril.Raw.SSA.Isotope.Institution.InstrSig
public import Silmaril.Raw.SSA.Isotope.Institution.LetSeqSig
public import Silmaril.Raw.SSA.Isotope.Theory.Models.Theories
public import Silmaril.Raw.SSA.Isotope.Morphism.Instructions.LetSeq

@[expose] public section

/-!
# The equational institution of exactly typed LetSeq

Fix a type universe `τ`, effects `ε`, variable names `ν` and a free-variable context
`Γ : Ctx ν τ`. The institution `LetSeq.inst Γ : InstrSig τ ε ⥤ Room` has

* signatures: primitive instruction signatures `P` with instruction relabellings;
* sentences over `P`: typed equations `β ⊢ a = b : A` in context `Γ`, between exactly typed
  locally nameless terms with data-valued derivations (the carriers of
  `LetSeq.LocallyNameless.Models.syntaxAlgebra`);
* models over `P`: all operation algebras of `LetSeq.LocallyNameless.Models.signature P Γ`;
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

namespace Silmaril.Isotope.Institution.LetSeq

open CategoryTheory
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory
open Silmaril.Isotope.Theory
open Silmaril.Isotope.LetSeq.LocallyNameless

universe u

variable {ν τ ε : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] (Γ : Ctx ν τ)

/-- Exact LetSeq syntax in context `Γ`, as a presented syntax. -/
def presObj (P : InstrSig τ ε) : PresSig.{u, u, u} where
  Idx := TypingIndex τ
  Sig := Models.signature P.Instr Γ
  Syn := Models.syntaxAlgebra P.Instr Γ
  isInitial := Models.syntaxIsInitial P.Instr Γ

/-- Instruction signatures to presented LetSeq syntax. -/
def pres : InstrSig τ ε ⥤ PresSig.{u, u, u} where
  obj := presObj Γ
  map g := sigHom Γ g
  map_id P := sigHom_id Γ P
  map_comp f g := sigHom_comp Γ f g

/-- The equational institution of exactly typed LetSeq in context `Γ`. -/
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

/-- The satisfaction condition of the LetSeq institution, read off the room functor. -/
theorem satisfaction {P Q : InstrSig τ ε} (g : P ⟶ Q)
    (M : ((inst (ε := ε) Γ).obj Q).Mod) (e : ((inst (ε := ε) Γ).obj P).Sen) :
    ((inst (ε := ε) Γ).obj Q).Sat M (((inst (ε := ε) Γ).map g).sen e) ↔
      ((inst (ε := ε) Γ).obj P).Sat ((((inst (ε := ε) Γ).map g)).mod.obj M) e :=
  Silmaril.Logic.Institution.satisfaction_condition (inst (ε := ε) Γ) g M e

/-! ### Translation is instruction relabelling -/

/-- A transported value is heterogeneously equal to the original. -/
theorem eqRec_heq_self {α : Sort*} {a : α} {motive : (x : α) → a = x → Sort*}
    (v : motive a rfl) {b : α} (h : a = b) : HEq (@Eq.rec α a motive v b h) v := by
  subst h
  rfl

/-- The syntax operation of an instruction symbol transported along an equation of result
types builds the instruction node on the (transported) argument term. -/
theorem syntaxOp_castOp_op_fst {Ψ : Type u} [HasTy Ψ τ] {n : Nat} {β : BoundCtx τ n} (f : Ψ)
    {A B : τ} (hA : instrSrc f = A) (hB : instrTrg f = B)
    (args : (j : Fin ((Models.signature Ψ Γ).arity
        (castOp (Models.signature Ψ Γ) (congrArg (fun C => (⟨n, β, C⟩ : TypingIndex τ)) hB)
          (Models.Operation.op (Γ := Γ) (β := β) f)))) →
      Models.Carrier Ψ Γ ((Models.signature Ψ Γ).argSort
        (castOp (Models.signature Ψ Γ) (congrArg (fun C => (⟨n, β, C⟩ : TypingIndex τ)) hB)
          (Models.Operation.op (Γ := Γ) (β := β) f)) j))
    (c : Models.Carrier Ψ Γ ⟨n, β, A⟩) (hc : ∀ j, HEq (args j) c) :
    (Models.syntaxOp (castOp (Models.signature Ψ Γ)
        (congrArg (fun C => (⟨n, β, C⟩ : TypingIndex τ)) hB)
        (Models.Operation.op (Γ := Γ) (β := β) f)) args).1 = Tm.op f c.1 := by
  subst hA hB
  exact congrArg (fun x : Models.Carrier Ψ Γ ⟨n, β, instrSrc f⟩ => Tm.op f x.1)
    (eq_of_heq (hc _))

/-- Structural interpretation into the reduct of the target syntax relabels instructions. -/
theorem denote_reduct_fst {P Q : InstrSig τ ε} (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν P.Instr n} {A : τ} (d : Derivation P.Instr Γ β t A) :
    (Models.denote (TheoryModel.Algebra.reductObj (sigHom Γ g)
        (Models.syntaxAlgebra Q.Instr Γ)) d).1 = Tm.mapInstr (InstrSig.Hom.instr g) t := by
  induction d with
  | fv _ => rfl
  | bv => rfl
  | unit => rfl
  | @op n β f a ha ih =>
      refine Eq.trans (syntaxOp_castOp_op_fst Γ (InstrSig.Hom.instr g f) (g.source f)
        (g.target f) _ (Models.denote (TheoryModel.Algebra.reductObj (sigHom Γ g)
          (Models.syntaxAlgebra Q.Instr Γ)) ha) ?_) ?_
      · exact fun _ => eqRec_heq_self _ _
      · exact congrArg (Tm.op (InstrSig.Hom.instr g f)) ih
  | let₁ _ _ iha ihb => exact congrArg₂ Tm.let₁ iha ihb
  | pair _ _ iha ihb => exact congrArg₂ Tm.pair iha ihb
  | let₂ _ _ iha ihb => exact congrArg₂ Tm.let₂ iha ihb

/-- The term component of a translated sentence is the existing instruction relabelling. -/
theorem translate_fst {P Q : InstrSig τ ε} (g : P ⟶ Q) {i : TypingIndex τ}
    (x : Models.Carrier P.Instr Γ i) :
    ((PresSig.translate ((pres (ε := ε) Γ).map g)).map x).1 = Tm.mapInstr (InstrSig.Hom.instr g) x.1 := by
  change (((Models.syntaxIsInitial P.Instr Γ).to
      (TheoryModel.Algebra.reductObj (sigHom Γ g) (Models.syntaxAlgebra Q.Instr Γ))).map x).1 = _
  rw [Models.syntaxIsInitial_to]
  exact denote_reduct_fst Γ g x.2

/-! ### Theories -/

variable {Γ}

/-- The sentences of the base exact equational theory of LetSeq. -/
abbrev baseSentences (pureEff : ε) (P : InstrSig τ ε) : Set ((inst (ε := ε) Γ).obj P).Sen :=
  PresSig.equations (X := (pres (ε := ε) Γ).obj P) (Models.equationCongruence pureEff Γ)

/-- Semantic consequence from the base theory is exact derivability. This is the institution
form of completeness of the quotient model (`PresSig.entails_equations_iff`, from
`TheoryModel.semantic_iff`); see `entails_base_iff_denote` for the form of
`LetSeq.LocallyNameless.Models.semantic_iff`. -/
theorem entails_base_iff (pureEff : ε) (P : InstrSig τ ε)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν P.Instr n} {A : τ}
    (da : Derivation P.Instr Γ β a A) (db : Derivation P.Instr Γ β b A) :
    ((inst (ε := ε) Γ).obj P).Entails (baseSentences pureEff P) ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ ↔
      Silmaril.Isotope.LetSeq.LocallyNameless.Equiv pureEff Γ β a b A :=
  PresSig.entails_equations_iff (X := (pres (ε := ε) Γ).obj P)
    (Models.equationCongruence pureEff Γ) ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩

/-- Semantic consequence from the base theory is equality of denotations in every existing
equational model: `entails_base_iff` composed with `LetSeq.LocallyNameless.Models.semantic_iff`. -/
theorem entails_base_iff_denote (pureEff : ε) (P : InstrSig τ ε)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν P.Instr n} {A : τ}
    (da : Derivation P.Instr Γ β a A) (db : Derivation P.Instr Γ β b A) :
    ((inst (ε := ε) Γ).obj P).Entails (baseSentences pureEff P) ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ ↔
      ∀ M : Models.EquationalModels (Φ := P.Instr) pureEff Γ,
        Models.denote M.algebra da = Models.denote M.algebra db :=
  (entails_base_iff pureEff P da db).trans (Models.semantic_iff da db)

/-- Semantic consequence from any equational theory is membership in it
(`PresSig.entails_equations_iff`); see `entails_theory_iff_denote` for the form of
`LetSeq.LocallyNameless.Models.theory_semantic_iff`. -/
theorem entails_theory_iff (P : InstrSig τ ε) (E : EquationalTheory (typedSyntax P.Instr Γ))
    {i : TypingIndex τ} (x y : Models.Carrier P.Instr Γ i) :
    ((inst (ε := ε) Γ).obj P).Entails
        (PresSig.equations (X := (pres (ε := ε) Γ).obj P) (Models.theoryCongruence E)) ⟨i, x, y⟩ ↔
      E.Rel (Models.eraseCarrier x) (Models.eraseCarrier y) :=
  PresSig.entails_equations_iff (X := (pres (ε := ε) Γ).obj P) (Models.theoryCongruence E)
    ⟨i, x, y⟩

/-- `entails_theory_iff` composed with `LetSeq.LocallyNameless.Models.theory_semantic_iff`. -/
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

/-- The base equational theory of LetSeq, as a theory of the institution. -/
def baseTheory (pureEff : ε) (P : InstrSig τ ε) : Silmaril.Logic.Institution.Theory (inst (ε := ε) Γ) :=
  theoryOf P (equationalTheory pureEff Γ)

/-- The base theory's sentences are those of `Models.equationCongruence`
(`Models.theoryCongruence_base`). -/
theorem baseTheory_sentences (pureEff : ε) (P : InstrSig τ ε) :
    (baseTheory pureEff P).sentences = baseSentences (Γ := Γ) pureEff P := by
  simp only [baseTheory, theoryOf, PresSig.theoryAt, Models.theoryCongruence_base]

/-- Instruction maps are theory morphisms of the base theories, by
`LetSeq.LocallyNameless.Equiv.mapInstr`. -/
def baseTheoryHom (pureEff : ε) {P Q : InstrSig τ ε} (g : P ⟶ Q) :
    baseTheory (Γ := Γ) pureEff P ⟶ baseTheory pureEff Q :=
  PresSig.theoryAtHom (pres (ε := ε) Γ) g (fun {i : TypingIndex τ} {x y : Models.Carrier P.Instr Γ i} h => by
    -- `LetSeq.LocallyNameless.Equiv.mapInstr` applied to `g.toSignatureMap`, with
    -- `translate_fst` identifying the translated terms.
    change Silmaril.Isotope.LetSeq.LocallyNameless.Equiv pureEff Γ i.bound
      ((PresSig.translate ((pres (ε := ε) Γ).map g)).map x).1
      ((PresSig.translate ((pres (ε := ε) Γ).map g)).map y).1 i.result
    rw [translate_fst, translate_fst]
    have h' : Silmaril.Isotope.LetSeq.LocallyNameless.Equiv pureEff Γ i.bound x.1 y.1 i.result := h
    have key := Silmaril.Isotope.LetSeq.LocallyNameless.Equiv.mapInstr g.toSignatureMap h'
    simp only [InstrSig.Hom.toSignatureMap, Ctx.mapTypes_id, BoundCtx.mapTypes_id, id_eq] at key
    exact key)

/-- The base theories, as a functor from instruction signatures to `Th(LetSeq.inst Γ)`. -/
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
    obtain ⟨a', rfl⟩ := Models.eraseCarrier_surjective i a
    obtain ⟨b', rfl⟩ := Models.eraseCarrier_surjective i b
    exact h (show (⟨i, a', b'⟩ : ((inst (ε := ε) Γ).obj P).Sen) ∈ (theoryOf P E).sentences
      from hab)
  · intro h e he
    exact h he

/-- The theory functor is full onto the theory morphisms over the identity signature morphism:
such a morphism comes from an inclusion of equational theories. -/
theorem theoryFunctor_full_over_id (P : InstrSig τ ε)
    {E E' : EquationalTheory (typedSyntax P.Instr Γ)}
    (f : (theoryFunctor (Γ := Γ) P).obj E ⟶ (theoryFunctor P).obj E')
    (hf : f.hom.sig = 𝟙 P) : ∃ h : E ⟶ E', (theoryFunctor P).map h = f := by
  have key : ∀ e, ((inst (ε := ε) Γ).map f.hom.sig).sen e = e := by
    intro e
    rw [hf]
    exact congrArg (fun c => Silmaril.Logic.Institution.Corridor.sen c e)
      ((inst (ε := ε) Γ).map_id P)
  have hle : E ≤ E' := by
    refine (theoryOf_sentences_subset_iff P E E').1 (fun e he => ?_)
    exact (congrArg (· ∈ (theoryOf P E').sentences) (key e)).mp (f.hom.mapsTo he)
  exact ⟨homOfLE hle, Silmaril.Logic.Institution.Theory.hom_ext hf.symm⟩

/-- The theory functor is injective on objects. -/
theorem theoryFunctor_obj_injective (P : InstrSig τ ε) :
    Function.Injective (theoryFunctor (Γ := Γ) P).obj := by
  intro E E' h
  have h0 : (⟨P, PresSig.equations (X := (pres (ε := ε) Γ).obj P) (Models.theoryCongruence E)⟩ :
        Silmaril.Logic.Institution.Presentation (inst (ε := ε) Γ)) =
      ⟨P, PresSig.equations (X := (pres (ε := ε) Γ).obj P) (Models.theoryCongruence E')⟩ :=
    congrArg (fun T : Silmaril.Logic.Institution.Theory (inst (ε := ε) Γ) => T.obj) h
  injection h0 with _ h2
  have h₁ : E ≤ E' := (theoryOf_sentences_subset_iff P E E').1 h2.subset
  have h₂ : E' ≤ E := (theoryOf_sentences_subset_iff P E' E).1 h2.symm.subset
  exact EquationalTheory.ext fun _ _ => ⟨h₁, h₂⟩

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

end Silmaril.Isotope.Institution.LetSeq
