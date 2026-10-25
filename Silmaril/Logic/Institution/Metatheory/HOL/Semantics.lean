module

public import Silmaril.Logic.Institution.Metatheory.HOL.Syntax

@[expose] public section

/-!
# Reducts of HOL models along signature extensions

The model side of `Metatheory.HOL`: the reduct `HOL.Model.reduct` of a `HOLLight.Model` along a
signature extension, and the satisfaction condition for sentences (`HOL.holds_reduct_iff`) and
sequents (`HOL.entails_reduct_iff`) for the existing semantics `HOLLight.Holds`,
`HOLLight.Entails`.
-/

namespace Silmaril.Logic.Institution.Metatheory

open CategoryTheory Silmaril.Logic.HOLLight

universe u

namespace HOL

/-- The reduct of a model along a signature extension: the same type model, and the constants
of the smaller signature interpreted as in the larger one. -/
def Model.reduct {S T : HolSig} (h : S ≤ T) (M : Model.{u} T.sig) : Model.{u} S.sig where
  toTypeModel := M.toTypeModel
  constant n s hs := M.constant n s (lookup_of_prefix h.2 hs)

/-- Well-formedness of types is preserved by extending the type operators (a self-contained
local copy of `HOL.Ty.wellFormed_of_prefix`, used for the reduct transfer). -/
private theorem wellFormed_of_prefix' {ops ops' : List Nat} (h : ops <+: ops') {A : Ty}
    (hA : A.WellFormed ops) : A.WellFormed ops' := by
  induction A using Ty.induction_on with
  | var i => simp [Ty.WellFormed]
  | bool => simp [Ty.WellFormed]
  | ind => simp [Ty.WellFormed]
  | arr A B ihA ihB =>
    simp only [Ty.WellFormed] at hA ⊢
    exact ⟨ihA hA.1, ihB hA.2⟩
  | app c args ih =>
    simp only [Ty.WellFormed, Ty.wellFormedList_iff] at hA ⊢
    exact ⟨lookup_of_prefix h hA.1, fun B hB => ih B hB (hA.2 B hB)⟩

/-- Constant evaluation in a reduct is constant evaluation in the original model. -/
private theorem constEval_of_reduct {S T : HolSig} (h : S ≤ T) (M : Model.{u} T.sig)
    {ρ : TypeValuation.{u}} {c : Const} {A : Ty} {v : Value (Model.reduct h M) ρ A}
    (hc : ConstEval (Model.reduct h M) ρ c A v) : ConstEval M ρ c A v := by
  cases hc with
  | eq wf => exact .eq (wellFormed_of_prefix' h.1 wf)
  | select wf => exact .select (wellFormed_of_prefix' h.1 wf)
  | user lookup scheme arity wf =>
    exact .user (lookup_of_prefix h.2 lookup)
      ⟨wellFormed_of_prefix' h.1 scheme.1, scheme.2⟩ arity
      (fun B hB => wellFormed_of_prefix' h.1 (wf B hB))

/-- Evaluation in a reduct is evaluation in the original model, with the same value. -/
private theorem eval_of_reduct {S T : HolSig} (h : S ≤ T) (M : Model.{u} T.sig)
    {ρ : TypeValuation.{u}} {ν : FreeEnv (Model.reduct h M) ρ} {Γ : List Ty}
    {η : BoundEnv (Model.reduct h M) ρ Γ} {t : Tm} {A : Ty} {v : Value (Model.reduct h M) ρ A}
    (he : Eval (Model.reduct h M) ρ ν η t A v) : Eval M ρ ν η t A v := by
  induction he with
  | bvar η lookup wf => exact Eval.bvar (M := M) η lookup (wellFormed_of_prefix' h.1 wf)
  | fvar η n wf => exact Eval.fvar (M := M) η n (wellFormed_of_prefix' h.1 wf)
  | const η hc => exact Eval.const (M := M) η (constEval_of_reduct h M hc)
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam wf _ ih => exact .lam (wellFormed_of_prefix' h.1 wf) ih

/-- Truth of a well-typed sentence is invariant under reducts along extensions (the HOL
satisfaction condition, at the level of `HOLLight.Holds`). -/
theorem holds_reduct_iff {S T : HolSig} (h : S ≤ T) (M : Model.{u} T.sig)
    (ρ : TypeValuation.{u}) (ν : FreeEnv M ρ) {p : Tm} (hp : HasType S.sig [] p .bool) :
    Holds (Model.reduct h M) ρ ν p ↔ Holds M ρ ν p := by
  constructor
  · rintro ⟨v, hv, ht⟩
    exact ⟨v, eval_of_reduct h M hv, ht⟩
  · rintro ⟨v, hv, ht⟩
    obtain ⟨w, hw⟩ := hp.eval_exists (Model.reduct h M) ρ ν BoundEnv.empty
    have hwv : w = v := (eval_of_reduct h M hw).unique hv
    exact ⟨w, hw, hwv ▸ ht⟩

/-- The satisfaction condition for sequents along a signature extension. -/
theorem entails_reduct_iff {S T : HolSig} (h : S ≤ T) (M : Model.{u} T.sig) (s : Seq S) :
    HOLLight.Entails M s.hyps s.concl ↔ HOLLight.Entails (Model.reduct h M) s.hyps s.concl := by
  have hyps : ∀ ρ ν, HypsTrue (Model.reduct h M) ρ ν s.hyps ↔ HypsTrue M ρ ν s.hyps :=
    fun ρ ν => forall₂_congr fun p hp => holds_reduct_iff h M ρ ν (s.typedHyps p hp)
  constructor
  · intro hE ρ ν hH
    exact (holds_reduct_iff h M ρ ν s.typing).mpr (hE ρ ν ((hyps ρ ν).mp hH))
  · intro hE ρ ν hH
    exact (holds_reduct_iff h M ρ ν s.typing).mp (hE ρ ν ((hyps ρ ν).mpr hH))

end HOL

end Silmaril.Logic.Institution.Metatheory
