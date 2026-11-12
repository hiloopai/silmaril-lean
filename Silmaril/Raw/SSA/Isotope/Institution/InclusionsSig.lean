module

public import Silmaril.Raw.SSA.Isotope.Institution.LetSeqSig
public import Silmaril.Raw.SSA.Isotope.Institution.LetCaseSig
public import Silmaril.Raw.SSA.Isotope.Institution.LetIterSig
public import Silmaril.Raw.SSA.Isotope.Morphism.Models

@[expose] public section

/-!
# Naturality of the calculus operation inclusions

The operation inclusions `Morphism.SeqCase.typedSignatureHom` and
`Morphism.CaseIter.typedSignatureHom` commute with instruction relabelling (`LetSeq.sigHom`,
`LetCase.sigHom`, `LetIter.sigHom`). These are the naturality squares of
`Silmaril.Isotope.Institution.seqCasePres` and `caseIterPres`.
-/

namespace Silmaril.Isotope.Institution

open CategoryTheory
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory
open Silmaril.Isotope.Theory

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν] (Γ : Ctx ν τ)

/-- The operation inclusion `LetSeq ⊆ LetCase` commutes with result-sort transport. -/
theorem seqCase_op_castOp_heq {Φ : Type u} [HasTy Φ τ] {i j : TypingIndex τ} (h : i = j)
    (o : (Silmaril.Isotope.LetSeq.LocallyNameless.Models.signature Φ Γ).Op i) :
    HEq ((Morphism.SeqCase.typedSignatureHom (Φ := Φ) Γ).op (castOp _ h o))
      ((Morphism.SeqCase.typedSignatureHom (Φ := Φ) Γ).op o) := by
  subst h
  rfl

/-- The operation inclusion `LetSeq ⊆ LetCase` keeps argument positions. -/
theorem seqCase_argVal {Φ : Type u} [HasTy Φ τ] :
    SigHomArgVal (Morphism.SeqCase.typedSignatureHom (Φ := Φ) Γ) := by
  intro i o j
  cases o <;> rfl

/-- The operation inclusion `LetCase ⊆ LetIter` commutes with result-sort transport. -/
theorem caseIter_op_castOp_heq {Φ : Type u} [HasTy Φ τ] {i j : TypingIndex τ} (h : i = j)
    (o : (Silmaril.Isotope.LetCase.LocallyNameless.Models.signature Φ Γ).Op i) :
    HEq ((Morphism.CaseIter.typedSignatureHom (Φ := Φ) Γ).op (castOp _ h o))
      ((Morphism.CaseIter.typedSignatureHom (Φ := Φ) Γ).op o) := by
  subst h
  rfl

/-- The operation inclusion `LetCase ⊆ LetIter` keeps argument positions. -/
theorem caseIter_argVal {Φ : Type u} [HasTy Φ τ] :
    SigHomArgVal (Morphism.CaseIter.typedSignatureHom (Φ := Φ) Γ) := by
  intro i o j
  cases o <;> rfl

/-- The inclusion `LetSeq ⊆ LetCase` of operations commutes with instruction relabelling. -/
theorem seqCase_sigHom_natural {P Q : InstrSig τ ε} (g : P ⟶ Q) :
    (Morphism.SeqCase.typedSignatureHom (Φ := Q.Instr) Γ).comp (LetSeq.sigHom Γ g) =
      (LetCase.sigHom Γ g).comp (Morphism.SeqCase.typedSignatureHom (Φ := P.Instr) Γ) := by
  refine sigHom_ext_of_argVal rfl ?_
    (sigHomArgVal_comp (seqCase_argVal Γ) (LetSeq.sigHom_argVal Γ g))
    (sigHomArgVal_comp (LetCase.sigHom_argVal Γ g) (seqCase_argVal Γ))
  intro i o
  cases o with
  | @op n β x =>
      have h1 : HEq ((Morphism.SeqCase.typedSignatureHom (Φ := Q.Instr) Γ).op
            (LetSeq.opMap Γ g
              (Silmaril.Isotope.LetSeq.LocallyNameless.Models.Operation.op (Γ := Γ) (β := β) x)))
          ((Morphism.SeqCase.typedSignatureHom (Φ := Q.Instr) Γ).op
            (Silmaril.Isotope.LetSeq.LocallyNameless.Models.Operation.op (Γ := Γ) (β := β)
              (g.instr x))) := by
        rw [LetSeq.opMap_op]
        exact seqCase_op_castOp_heq Γ _ _
      exact h1.trans (LetCase.opMap_op_heq Γ g x).symm
  | _ => exact HEq.rfl

/-- The inclusion `LetCase ⊆ LetIter` of operations commutes with instruction relabelling. -/
theorem caseIter_sigHom_natural {P Q : InstrSig τ ε} (g : P ⟶ Q) :
    (Morphism.CaseIter.typedSignatureHom (Φ := Q.Instr) Γ).comp (LetCase.sigHom Γ g) =
      (LetIter.sigHom Γ g).comp (Morphism.CaseIter.typedSignatureHom (Φ := P.Instr) Γ) := by
  refine sigHom_ext_of_argVal rfl ?_
    (sigHomArgVal_comp (caseIter_argVal Γ) (LetCase.sigHom_argVal Γ g))
    (sigHomArgVal_comp (LetIter.sigHom_argVal Γ g) (caseIter_argVal Γ))
  intro i o
  cases o with
  | @op n β x =>
      have h1 : HEq ((Morphism.CaseIter.typedSignatureHom (Φ := Q.Instr) Γ).op
            (LetCase.opMap Γ g
              (Silmaril.Isotope.LetCase.LocallyNameless.Models.Operation.op (Γ := Γ) (β := β) x)))
          ((Morphism.CaseIter.typedSignatureHom (Φ := Q.Instr) Γ).op
            (Silmaril.Isotope.LetCase.LocallyNameless.Models.Operation.op (Γ := Γ) (β := β)
              (g.instr x))) := by
        rw [LetCase.opMap_op]
        exact caseIter_op_castOp_heq Γ _ _
      exact h1.trans (LetIter.opMap_op_heq Γ g x).symm
  | _ => exact HEq.rfl

end Silmaril.Isotope.Institution
