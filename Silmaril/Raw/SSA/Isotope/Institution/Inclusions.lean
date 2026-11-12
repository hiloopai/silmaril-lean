module

public import Silmaril.Raw.SSA.Isotope.Institution.LetSeq
public import Silmaril.Raw.SSA.Isotope.Institution.LetCase
public import Silmaril.Raw.SSA.Isotope.Institution.LetIter
public import Silmaril.Raw.SSA.Isotope.Institution.InclusionsSig
public import Silmaril.Raw.SSA.Isotope.Morphism.Models
public import Silmaril.Raw.SSA.Isotope.Morphism.Theory
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section

/-!
# The calculus inclusions as institution comorphisms

The inclusions `LetSeq ⊆ LetCase ⊆ LetIter` act on the equational institutions of
`Silmaril.Isotope.Institution.{LetSeq,LetCase,LetIter}` as follows, at every instruction
signature `P` and free-variable context `Γ`:

* sentences go *forwards*: an equation of the smaller calculus is sent to the equation between
  the embedded terms (`Morphism.SeqCase.embed` with the derivation translation
  `Morphism.SeqCase.typedAlgebraHom`);
* models go *backwards*: an algebra of the larger calculus restricts to the smaller one by
  forgetting the added operations (`TheoryModel.Algebra.reduct` along the existing operation
  inclusion `Morphism.SeqCase.typedSignatureHom`, the same functor as
  `Morphism.SeqCase.typedModelRestriction` on models of theories).

Sentences and models therefore travel in opposite directions *over the identity functor of
instruction signatures*, which is the shape of an institution **comorphism**
`LetSeq → LetCase` (`ρ : I_Seq ⟶ 𝟭 ⋙ I_Case`). Because the signature functor is the identity,
the same natural transformation is also an institution **morphism** `LetCase → LetSeq`
(`η : 𝟭 ⋙ I_Seq ⟶ I_Case`): both readings are recorded (`seqCaseCoHom`, `seqCaseHom`). The
comorphism reading is the primary one: it is the direction of the term embedding.

Both are obtained by whiskering a natural transformation of presented syntaxes
`LetSeq.pres Γ ⟶ LetCase.pres Γ` with the presented-syntax institution `PresSig.inst`, so the
satisfaction condition is again `TheoryModel.reindex_fold_map`.

Model expansion. The restriction is not surjective in general: a `LetSeq` algebra may have an
empty carrier at a sort `A + B` and a nonempty carrier at `A`, and then admits no `inl`. It is
surjective onto the *inhabited* algebras (all carriers nonempty), by choosing arbitrary values
for the added operations (`seqCase_expand`). Borrowing (`seqCase_entails_iff`) is stated under
the corresponding hypothesis that inhabited countermodels suffice.
-/

namespace Silmaril.Isotope.Institution

open CategoryTheory
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory
open Silmaril.Isotope.Theory

universe u w m₁ m₂

/-! ### Borrowing along a partially model-expansive corridor -/

/-- Borrowing for a corridor that is model-expansive only on models satisfying `Q`, given that
every countermodel can be replaced by one satisfying `Q`. Generalizes
`Corridor.entails_map_iff` (the case `Q = ⊤`). -/
theorem entails_map_iff_of_expand {R₁ R₂ : Room.{w, m₁, m₂}} (c : R₁ ⟶ R₂) (Q : R₁.Mod → Prop)
    (hexp : ∀ M, Q M → ∃ N, c.mod.obj N = M) (Δ : Set R₁.Sen) (φ : R₁.Sen)
    (h : ∀ M ∈ R₁.modelsOf Δ, ¬ R₁.Sat M φ → ∃ M' ∈ R₁.modelsOf Δ, Q M' ∧ ¬ R₁.Sat M' φ) :
    R₁.Entails Δ φ ↔ R₂.Entails (c.sen '' Δ) (c.sen φ) := by
  refine ⟨c.entails_map, fun hE M hM => ?_⟩
  by_contra hφ
  obtain ⟨M', hM', hQ, hφ'⟩ := h M hM hφ
  obtain ⟨N, rfl⟩ := hexp M' hQ
  refine hφ' ((c.sat N φ).1 (hE N ?_))
  rintro _ ⟨χ, hχ, rfl⟩
  exact (c.sat N χ).2 (hM' χ hχ)

/-! ### Equality of algebras with a common carrier -/

/-- Two algebras with the same carriers are equal when their operations agree pointwise. -/
theorem algebra_eq_of_op {I : Type u} {Sig : TheoryModel.Signature.{u, u} I} {C : I → Type u}
    {op op' : {i : I} → (o : Sig.Op i) → ((j : Fin (Sig.arity o)) → C (Sig.argSort o j)) → C i}
    (h : ∀ (i : I) (o : Sig.Op i) (args : (j : Fin (Sig.arity o)) → C (Sig.argSort o j)),
      op o args = op' o args) :
    (⟨C, op⟩ : TheoryModel.Algebra.{u, u, u} Sig) = ⟨C, op'⟩ := by
  have : @op = @op' := by
    funext i o args
    exact h i o args
  subst this
  rfl

/-! ### The equational institutions, as objects of `Inst` -/

section Insts

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν] (Γ : Ctx ν τ)

/-- The equational institution of LetSeq in context `Γ`. -/
def seqInst : Inst.{u + 1, u, u, u, u + 1} := ⟨InstrSig τ ε, LetSeq.inst Γ⟩

/-- The equational institution of LetCase in context `Γ`. -/
def caseInst : Inst.{u + 1, u, u, u, u + 1} := ⟨InstrSig τ ε, LetCase.inst Γ⟩

/-- The equational institution of LetIter in context `Γ`. -/
def iterInst : Inst.{u + 1, u, u, u, u + 1} := ⟨InstrSig τ ε, LetIter.inst Γ⟩

end Insts

/-! ### LetSeq ⊆ LetCase -/

section SeqCase

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν] (Γ : Ctx ν τ)

/-- The operation inclusion `Morphism.SeqCase.typedSignatureHom`, natural in the instruction
signature. -/
def seqCasePres : LetSeq.pres (ε := ε) Γ ⟶ LetCase.pres (ε := ε) Γ where
  app P := Morphism.SeqCase.typedSignatureHom (Φ := P.Instr) Γ
  naturality _ _ g := seqCase_sigHom_natural Γ g

/-- The inclusion `LetSeq ⊆ LetCase` as a natural transformation of room functors. -/
def seqCaseRho : LetSeq.inst (ε := ε) Γ ⟶ LetCase.inst (ε := ε) Γ :=
  Functor.whiskerRight (seqCasePres Γ) PresSig.inst

/-- The inclusion `LetSeq ⊆ LetCase` as an institution comorphism over the identity of
instruction signatures. -/
def seqCaseCoHom : Inst.CoHom (seqInst (ε := ε) Γ) (caseInst (ε := ε) Γ) :=
  ⟨𝟭 _, seqCaseRho Γ ≫ (Functor.leftUnitor _).inv⟩

/-- The same data read as an institution morphism `LetCase → LetSeq`. -/
def seqCaseHom : Inst.Hom (caseInst (ε := ε) Γ) (seqInst (ε := ε) Γ) :=
  ⟨𝟭 _, (Functor.leftUnitor _).hom ≫ seqCaseRho Γ⟩

/-- The sentence translation of the comorphism is the existing term embedding
`Morphism.SeqCase.embed`, with the derivation translation of
`Morphism.SeqCase.typedAlgebraHom` (by initiality of the `LetSeq` syntax). -/
theorem seqCase_sen (P : InstrSig τ ε) (e : ((LetSeq.inst (ε := ε) Γ).obj P).Sen) :
    ((seqCaseRho (ε := ε) Γ).app P).sen e =
      ⟨e.1, (Morphism.SeqCase.typedAlgebraHom (Φ := P.Instr) Γ).map e.2.1,
        (Morphism.SeqCase.typedAlgebraHom (Φ := P.Instr) Γ).map e.2.2⟩ := by
  have h : PresSig.translate ((seqCasePres (ε := ε) Γ).app P) =
      Morphism.SeqCase.typedAlgebraHom (Φ := P.Instr) Γ :=
    ((LetSeq.pres (ε := ε) Γ).obj P).isInitial.hom_ext _ _
  show PresSig.mapEquation ((seqCasePres (ε := ε) Γ).app P) e = _
  unfold PresSig.mapEquation
  rw [h]
  rfl

/-- The model translation of the comorphism is the existing restriction: on models of theories
it is `Morphism.SeqCase.typedModelRestriction`. -/
theorem seqCase_mod_obj (P : InstrSig τ ε)
    (M : ((LetCase.inst (ε := ε) Γ).obj P).Mod) :
    ((seqCaseRho (ε := ε) Γ).app P).mod.obj M =
      TheoryModel.Algebra.reductObj (Morphism.SeqCase.typedSignatureHom (Φ := P.Instr) Γ) M :=
  rfl

/-- The satisfaction condition of the comorphism, from `Inst.CoHom.satisfaction`. -/
theorem seqCase_satisfaction (P : InstrSig τ ε) (M : ((LetCase.inst (ε := ε) Γ).obj P).Mod)
    (e : ((LetSeq.inst (ε := ε) Γ).obj P).Sen) :
    ((LetCase.inst (ε := ε) Γ).obj P).Sat M (((seqCaseRho (ε := ε) Γ).app P).sen e) ↔
      ((LetSeq.inst (ε := ε) Γ).obj P).Sat (((seqCaseRho (ε := ε) Γ).app P).mod.obj M) e :=
  ((seqCaseRho (ε := ε) Γ).app P).sat M e

/-- An inhabited `LetSeq` algebra (all carriers nonempty) extends to a `LetCase` algebra:
the added operations take arbitrary values. -/
noncomputable def seqCaseExpand (P : InstrSig τ ε)
    (M : TheoryModel.Algebra.{u, u, u} (LetSeq.LocallyNameless.Models.signature P.Instr Γ))
    (hM : ∀ i, Nonempty (M.Carrier i)) :
    TheoryModel.Algebra.{u, u, u} (LetCase.LocallyNameless.Models.signature P.Instr Γ) where
  Carrier := M.Carrier
  op {i} o args := match i, o, args with
    | _, .fv h, _ => M.op (.fv h) (fun j => Fin.elim0 j)
    | _, .bv k, _ => M.op (.bv k) (fun j => Fin.elim0 j)
    | _, .op f, a => M.op (.op f) a
    | _, .let₁ A B, a => M.op (.let₁ A B) a
    | _, .unit, _ => M.op .unit (fun j => Fin.elim0 j)
    | _, .pair A B, a => M.op (.pair A B) a
    | _, .let₂ A B C, a => M.op (.let₂ A B C) a
    | _, .inl _ _, _ => Classical.choice (hM _)
    | _, .inr _ _, _ => Classical.choice (hM _)
    | _, .case _ _ _, _ => Classical.choice (hM _)
    | _, .abort _, _ => Classical.choice (hM _)

/-- Model expansion: the restriction of `seqCaseExpand M` is `M`. -/
theorem seqCase_expand (P : InstrSig τ ε)
    (M : TheoryModel.Algebra.{u, u, u} (LetSeq.LocallyNameless.Models.signature P.Instr Γ))
    (hM : ∀ i, Nonempty (M.Carrier i)) :
    ((seqCaseRho (ε := ε) Γ).app P).mod.obj (seqCaseExpand Γ P M hM) = M := by
  obtain ⟨C, op⟩ := M
  refine algebra_eq_of_op (fun i o args => ?_)
  cases o <;> first
    | rfl
    | (show op _ _ = op _ _; exact congrArg _ (funext fun j => Fin.elim0 j))

/-- Borrowing: semantic consequence in `LetSeq` is semantic consequence of the embedded
equations in `LetCase`, whenever inhabited countermodels suffice. -/
theorem seqCase_entails_iff (P : InstrSig τ ε) (Δ : Set ((LetSeq.inst (ε := ε) Γ).obj P).Sen)
    (φ : ((LetSeq.inst (ε := ε) Γ).obj P).Sen)
    (h : ∀ M ∈ ((LetSeq.inst (ε := ε) Γ).obj P).modelsOf Δ,
      ¬ ((LetSeq.inst (ε := ε) Γ).obj P).Sat M φ →
        ∃ M' ∈ ((LetSeq.inst (ε := ε) Γ).obj P).modelsOf Δ,
          (∀ i, Nonempty (TheoryModel.Algebra.Carrier M' i)) ∧
            ¬ ((LetSeq.inst (ε := ε) Γ).obj P).Sat M' φ) :
    ((LetSeq.inst (ε := ε) Γ).obj P).Entails Δ φ ↔
      ((LetCase.inst (ε := ε) Γ).obj P).Entails (((seqCaseRho (ε := ε) Γ).app P).sen '' Δ)
        (((seqCaseRho (ε := ε) Γ).app P).sen φ) :=
  entails_map_iff_of_expand ((seqCaseRho (ε := ε) Γ).app P)
    (fun M => ∀ i, Nonempty (TheoryModel.Algebra.Carrier M i))
    (fun M hM => ⟨seqCaseExpand Γ P M hM, seqCase_expand Γ P M hM⟩) Δ φ h

/-- Exact `LetSeq` equations remain valid in the `LetCase` base theory after embedding. The
institution form of `Morphism.SeqCase.embed_equiv`. -/
theorem seqCase_entails_base (pureEff : ε) (P : InstrSig τ ε)
    (e : ((LetSeq.inst (ε := ε) Γ).obj P).Sen)
    (he : ((LetSeq.inst (ε := ε) Γ).obj P).Entails (LetSeq.baseSentences (Γ := Γ) pureEff P) e) :
    ((LetCase.inst (ε := ε) Γ).obj P).Entails (LetCase.baseSentences (Γ := Γ) pureEff P)
      (((seqCaseRho (ε := ε) Γ).app P).sen e) := by
  rw [seqCase_sen]
  obtain ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ := e
  exact (LetCase.entails_base_iff pureEff P (Morphism.SeqCase.derivation da)
    (Morphism.SeqCase.derivation db)).2
    (Morphism.SeqCase.embed_equiv ((LetSeq.entails_base_iff pureEff P da db).1 he))

end SeqCase

/-! ### LetCase ⊆ LetIter -/

section CaseIter

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν] (Γ : Ctx ν τ)

/-- The operation inclusion `Morphism.CaseIter.typedSignatureHom`, natural in the instruction
signature. -/
def caseIterPres : LetCase.pres (ε := ε) Γ ⟶ LetIter.pres (ε := ε) Γ where
  app P := Morphism.CaseIter.typedSignatureHom (Φ := P.Instr) Γ
  naturality _ _ g := caseIter_sigHom_natural Γ g

/-- The inclusion `LetCase ⊆ LetIter` as a natural transformation of room functors. -/
def caseIterRho : LetCase.inst (ε := ε) Γ ⟶ LetIter.inst (ε := ε) Γ :=
  Functor.whiskerRight (caseIterPres Γ) PresSig.inst

/-- The inclusion `LetCase ⊆ LetIter` as an institution comorphism. -/
def caseIterCoHom : Inst.CoHom (caseInst (ε := ε) Γ) (iterInst (ε := ε) Γ) :=
  ⟨𝟭 _, caseIterRho Γ ≫ (Functor.leftUnitor _).inv⟩

/-- The same data read as an institution morphism `LetIter → LetCase`. -/
def caseIterHom : Inst.Hom (iterInst (ε := ε) Γ) (caseInst (ε := ε) Γ) :=
  ⟨𝟭 _, (Functor.leftUnitor _).hom ≫ caseIterRho Γ⟩

/-- The sentence translation is the existing embedding (`Morphism.CaseIter.typedAlgebraHom`). -/
theorem caseIter_sen (P : InstrSig τ ε) (e : ((LetCase.inst (ε := ε) Γ).obj P).Sen) :
    ((caseIterRho (ε := ε) Γ).app P).sen e =
      ⟨e.1, (Morphism.CaseIter.typedAlgebraHom (Φ := P.Instr) Γ).map e.2.1,
        (Morphism.CaseIter.typedAlgebraHom (Φ := P.Instr) Γ).map e.2.2⟩ := by
  have h : PresSig.translate ((caseIterPres (ε := ε) Γ).app P) =
      Morphism.CaseIter.typedAlgebraHom (Φ := P.Instr) Γ :=
    ((LetCase.pres (ε := ε) Γ).obj P).isInitial.hom_ext _ _
  show PresSig.mapEquation ((caseIterPres (ε := ε) Γ).app P) e = _
  unfold PresSig.mapEquation
  rw [h]
  rfl

/-- An inhabited `LetCase` algebra extends to a `LetIter` algebra. -/
noncomputable def caseIterExpand (P : InstrSig τ ε)
    (M : TheoryModel.Algebra.{u, u, u} (LetCase.LocallyNameless.Models.signature P.Instr Γ))
    (hM : ∀ i, Nonempty (M.Carrier i)) :
    TheoryModel.Algebra.{u, u, u} (LetIter.LocallyNameless.Models.signature P.Instr Γ) where
  Carrier := M.Carrier
  op {i} o args := match i, o, args with
    | _, .fv h, _ => M.op (.fv h) (fun j => Fin.elim0 j)
    | _, .bv k, _ => M.op (.bv k) (fun j => Fin.elim0 j)
    | _, .op f, a => M.op (.op f) a
    | _, .let₁ A B, a => M.op (.let₁ A B) a
    | _, .unit, _ => M.op .unit (fun j => Fin.elim0 j)
    | _, .pair A B, a => M.op (.pair A B) a
    | _, .let₂ A B C, a => M.op (.let₂ A B C) a
    | _, .inl A B, a => M.op (.inl A B) a
    | _, .inr A B, a => M.op (.inr A B) a
    | _, .case A B C, a => M.op (.case A B C) a
    | _, .abort C, a => M.op (.abort C) a
    | _, .iter _ _, _ => Classical.choice (hM _)

/-- Model expansion: the restriction of `caseIterExpand M` is `M`. -/
theorem caseIter_expand (P : InstrSig τ ε)
    (M : TheoryModel.Algebra.{u, u, u} (LetCase.LocallyNameless.Models.signature P.Instr Γ))
    (hM : ∀ i, Nonempty (M.Carrier i)) :
    ((caseIterRho (ε := ε) Γ).app P).mod.obj (caseIterExpand Γ P M hM) = M := by
  obtain ⟨C, op⟩ := M
  refine algebra_eq_of_op (fun i o args => ?_)
  cases o <;> first
    | rfl
    | (show op _ _ = op _ _; exact congrArg _ (funext fun j => Fin.elim0 j))

/-- Borrowing along `LetCase ⊆ LetIter`, whenever inhabited countermodels suffice. -/
theorem caseIter_entails_iff (P : InstrSig τ ε) (Δ : Set ((LetCase.inst (ε := ε) Γ).obj P).Sen)
    (φ : ((LetCase.inst (ε := ε) Γ).obj P).Sen)
    (h : ∀ M ∈ ((LetCase.inst (ε := ε) Γ).obj P).modelsOf Δ,
      ¬ ((LetCase.inst (ε := ε) Γ).obj P).Sat M φ →
        ∃ M' ∈ ((LetCase.inst (ε := ε) Γ).obj P).modelsOf Δ,
          (∀ i, Nonempty (TheoryModel.Algebra.Carrier M' i)) ∧
            ¬ ((LetCase.inst (ε := ε) Γ).obj P).Sat M' φ) :
    ((LetCase.inst (ε := ε) Γ).obj P).Entails Δ φ ↔
      ((LetIter.inst (ε := ε) Γ).obj P).Entails (((caseIterRho (ε := ε) Γ).app P).sen '' Δ)
        (((caseIterRho (ε := ε) Γ).app P).sen φ) :=
  entails_map_iff_of_expand ((caseIterRho (ε := ε) Γ).app P)
    (fun M => ∀ i, Nonempty (TheoryModel.Algebra.Carrier M i))
    (fun M hM => ⟨caseIterExpand Γ P M hM, caseIter_expand Γ P M hM⟩) Δ φ h

/-- Exact `LetCase` equations remain valid in the `LetIter` base theory after embedding. The
institution form of `Morphism.CaseIter.embed_equiv`. -/
theorem caseIter_entails_base (pureEff : ε) (P : InstrSig τ ε)
    (e : ((LetCase.inst (ε := ε) Γ).obj P).Sen)
    (he : ((LetCase.inst (ε := ε) Γ).obj P).Entails (LetCase.baseSentences (Γ := Γ) pureEff P) e) :
    ((LetIter.inst (ε := ε) Γ).obj P).Entails (LetIter.baseSentences (Γ := Γ) pureEff P)
      (((caseIterRho (ε := ε) Γ).app P).sen e) := by
  rw [caseIter_sen]
  obtain ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ := e
  exact (LetIter.entails_base_iff pureEff P (Morphism.CaseIter.derivation da)
    (Morphism.CaseIter.derivation db)).2
    (Morphism.CaseIter.embed_equiv ((LetCase.entails_base_iff pureEff P da db).1 he))

/-- The composite inclusion `LetSeq ⊆ LetIter`. -/
def seqIterCoHom : Inst.CoHom (seqInst (ε := ε) Γ) (iterInst (ε := ε) Γ) :=
  (seqCaseCoHom Γ).comp (caseIterCoHom Γ)

end CaseIter

end Silmaril.Isotope.Institution
