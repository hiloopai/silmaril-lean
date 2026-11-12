module

public import Silmaril.Raw.SSA.Isotope.Institution.Inclusions

@[expose] public section

/-!
# Unconditional borrowing along the calculus inclusions

`Silmaril.Isotope.Institution.Inclusions` proves borrowing along `LetSeq ⊆ LetCase` and
`LetCase ⊆ LetIter` under the hypothesis that inhabited countermodels suffice
(`seqCase_entails_iff`, `caseIter_entails_iff`). That hypothesis always holds: adjoining a junk
point to every carrier (`PresSig.withJunk`) turns any algebra into an inhabited one that
satisfies exactly the same equations, because the fold of the syntax factors through the
inclusion `some : M ⟶ withJunk M` (`PresSig.fold_withJunk`). So both borrowing theorems hold
outright (`seqCase_entails_iff_of_any`, `caseIter_entails_iff_of_any`).

The same file records that the equational institutions are not vacuous: the syntax algebra
itself is a model, and it satisfies an equation exactly when the two sides are equal
(`PresSig.holds_syn_iff`). So every equation between distinct syntax elements fails in some
model.
-/

namespace Silmaril.Isotope.Institution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory

universe u a b c

namespace PresSig

/-! ### Adjoining a junk point -/

section Junk

variable {I : Type a} {Sig : TheoryModel.Signature.{a, b} I}

open Classical in
/-- Adjoin a junk point `none` to every carrier. An operation returns the original value when
all its arguments are original, and `none` otherwise. -/
noncomputable def withJunk (M : TheoryModel.Algebra.{a, b, c} Sig) :
    TheoryModel.Algebra.{a, b, c} Sig where
  Carrier i := Option (M.Carrier i)
  op o args := if h : ∀ j, (args j).isSome then some (M.op o fun j => (args j).get (h j))
    else none

/-- The inclusion of an algebra into its junk extension is a homomorphism. -/
noncomputable def someHom (M : TheoryModel.Algebra.{a, b, c} Sig) : M ⟶ withJunk M where
  map x := some x
  comm o args := by
    simp [withJunk]

/-- Every carrier of the junk extension is inhabited. -/
theorem withJunk_nonempty (M : TheoryModel.Algebra.{a, b, c} Sig) (i : I) :
    Nonempty ((withJunk M).Carrier i) :=
  ⟨none⟩

end Junk

variable {X : PresSig.{a, b, c}}

/-- The fold into the junk extension is the fold into `M` followed by `some`. -/
theorem fold_withJunk (M : TheoryModel.Algebra.{a, b, c} X.Sig) {i : X.Idx}
    (x : X.Syn.Carrier i) :
    (X.isInitial.to (withJunk M)).map x = some ((X.isInitial.to M).map x) := by
  rw [X.isInitial.hom_ext (X.isInitial.to (withJunk M)) (X.isInitial.to M ≫ someHom M),
    TheoryModel.Algebra.comp_map]
  rfl

/-- The junk extension satisfies exactly the equations that `M` satisfies. -/
theorem holds_withJunk_iff (M : TheoryModel.Algebra.{a, b, c} X.Sig) (e : X.Equation) :
    X.Holds (withJunk M) e ↔ X.Holds M e := by
  show (X.isInitial.to (withJunk M)).map e.2.1 = (X.isInitial.to (withJunk M)).map e.2.2 ↔
    (X.isInitial.to M).map e.2.1 = (X.isInitial.to M).map e.2.2
  rw [fold_withJunk, fold_withJunk]
  exact Option.some_inj

/-- Every countermodel can be replaced by an inhabited one: the junk extension. -/
theorem exists_inhabited_countermodel (Δ : Set X.Equation) (φ : X.Equation)
    (M : (inst.obj X).Mod) (hM : M ∈ (inst.obj X).modelsOf Δ) (hφ : ¬ (inst.obj X).Sat M φ) :
    ∃ M' ∈ (inst.obj X).modelsOf Δ,
      (∀ i, Nonempty (TheoryModel.Algebra.Carrier M' i)) ∧ ¬ (inst.obj X).Sat M' φ :=
  ⟨withJunk M, fun e he => (holds_withJunk_iff M e).2 (hM e he), withJunk_nonempty M,
    fun h => hφ ((holds_withJunk_iff M φ).1 h)⟩

/-! ### Non-vacuity -/

/-- The fold of the syntax into itself is the identity. -/
theorem fold_syn (X : PresSig.{a, b, c}) {i : X.Idx} (x : X.Syn.Carrier i) :
    (X.isInitial.to X.Syn).map x = x :=
  congrArg (fun k : X.Syn ⟶ X.Syn => k.map x) (X.isInitial.hom_ext (X.isInitial.to X.Syn) (𝟙 _))

/-- The syntax algebra is a model satisfying an equation exactly when its sides are equal. So
the institution has models, and no equation between distinct syntax elements is valid. -/
theorem holds_syn_iff (X : PresSig.{a, b, c}) (e : X.Equation) :
    X.Holds X.Syn e ↔ e.2.1 = e.2.2 := by
  show (X.isInitial.to X.Syn).map e.2.1 = (X.isInitial.to X.Syn).map e.2.2 ↔ _
  rw [fold_syn, fold_syn]

/-- An equation between distinct syntax elements is not a consequence of the empty theory. -/
theorem not_entails_empty_of_ne (e : X.Equation) (h : e.2.1 ≠ e.2.2) :
    ¬ (inst.obj X).Entails ∅ e :=
  fun hE => h ((holds_syn_iff X e).1 (hE X.Syn fun _ hψ => hψ.elim))

end PresSig

/-! ### Borrowing without hypotheses -/

section SeqCase

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν] (Γ : Ctx ν τ)

/-- Borrowing along `LetSeq ⊆ LetCase`, with no hypothesis: semantic consequence in `LetSeq` is
semantic consequence of the embedded equations in `LetCase`. Proved from
`seqCase_entails_iff`, discharging its hypothesis by `PresSig.exists_inhabited_countermodel`. -/
theorem seqCase_entails_iff_of_any (P : InstrSig τ ε)
    (Δ : Set ((LetSeq.inst (ε := ε) Γ).obj P).Sen) (φ : ((LetSeq.inst (ε := ε) Γ).obj P).Sen) :
    ((LetSeq.inst (ε := ε) Γ).obj P).Entails Δ φ ↔
      ((LetCase.inst (ε := ε) Γ).obj P).Entails (((seqCaseRho (ε := ε) Γ).app P).sen '' Δ)
        (((seqCaseRho (ε := ε) Γ).app P).sen φ) :=
  seqCase_entails_iff Γ P Δ φ fun M hM hφ =>
    PresSig.exists_inhabited_countermodel (X := (LetSeq.pres (ε := ε) Γ).obj P) Δ φ M hM hφ

/-- Borrowing along `LetCase ⊆ LetIter`, with no hypothesis. Proved from
`caseIter_entails_iff`, discharging its hypothesis by `PresSig.exists_inhabited_countermodel`. -/
theorem caseIter_entails_iff_of_any (P : InstrSig τ ε)
    (Δ : Set ((LetCase.inst (ε := ε) Γ).obj P).Sen) (φ : ((LetCase.inst (ε := ε) Γ).obj P).Sen) :
    ((LetCase.inst (ε := ε) Γ).obj P).Entails Δ φ ↔
      ((LetIter.inst (ε := ε) Γ).obj P).Entails (((caseIterRho (ε := ε) Γ).app P).sen '' Δ)
        (((caseIterRho (ε := ε) Γ).app P).sen φ) :=
  caseIter_entails_iff Γ P Δ φ fun M hM hφ =>
    PresSig.exists_inhabited_countermodel (X := (LetCase.pres (ε := ε) Γ).obj P) Δ φ M hM hφ

end SeqCase

end Silmaril.Isotope.Institution
