module

public import Silmaril.Proofs.SSA.Isotope.Bridge.Syntax

/-!
# Bridge between legacy and thesis let-iter: purity and typing (proofs)

Under `TypeCompat` and `InstrCompat`, legacy (Prop-valued) typing of a term holds exactly
when the translated term has a (Type-valued) thesis typing derivation in the translated
contexts; under `EffCompat`, syntactic purity is preserved and reflected. Restated in
`Silmaril.SSA.Isotope.Bridge.Thms`.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Proofs.SSA.Isotope.Bridge

open Silmaril.Isotope.Bridge

local notation "LTm" => Silmaril.Isotope.LetIter.LocallyNameless.Tm
local notation "TTm" => Silmaril.Thesis.LambdaIter.LocallyNameless.Tm

variable {τ : Type u} [Silmaril.TypeFormers τ] [Silmaril.Thesis.LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [Silmaril.HasTy Φ τ] [Silmaril.Thesis.LambdaIter.HasTy Φ τ]
variable {ε : Type r} [Silmaril.HasEff Φ ε] [Silmaril.Thesis.LambdaIter.HasEff Φ ε]

/-! ## Purity -/

omit [DecidableEq ν] in
theorem pure_toThesis (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {t : LTm ν Φ n}
    (h : Silmaril.Isotope.LetIter.LocallyNameless.Pure pe t) :
    Silmaril.Thesis.LambdaIter.LocallyNameless.Pure pe (toThesis t) := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op ((hE.eff _).symm.trans hf) ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

omit [DecidableEq ν] in
theorem pure_ofThesis (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {t : TTm ν Φ n}
    (h : Silmaril.Thesis.LambdaIter.LocallyNameless.Pure pe t) :
    Silmaril.Isotope.LetIter.LocallyNameless.Pure pe (ofThesis t) := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op ((hE.eff _).trans hf) ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

omit [DecidableEq ν] in
theorem pure_iff (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {t : LTm ν Φ n} :
    Silmaril.Isotope.LetIter.LocallyNameless.Pure pe t ↔
      Silmaril.Thesis.LambdaIter.LocallyNameless.Pure pe (toThesis t) :=
  ⟨pure_toThesis hE pe, fun h => by simpa only [ofThesis_toThesis] using pure_ofThesis hE pe h⟩

/-! ## Typing -/

theorem hasType_toThesis (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    {Γ : Silmaril.Isotope.Ctx ν τ} {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {t : LTm ν Φ n} {A : τ}
    (h : Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ Γ β t A) :
    Nonempty (Silmaril.Thesis.LambdaIter.LocallyNameless.HasType Φ (Ctx.toThesis Γ)
      (BoundCtx.toThesis β) (toThesis t) A) := by
  induction h with
  | fv hx => exact ⟨.fv (by rw [Ctx.lookup_toThesis]; exact hx)⟩
  | bv => rw [← BoundCtx.get_toThesis]; exact ⟨.bv⟩
  | op _ ih =>
      obtain ⟨d⟩ := ih
      rw [hI.src] at d
      rw [hI.trg]
      exact ⟨.op d⟩
  | let₁ _ _ iha ihb =>
      obtain ⟨da⟩ := iha
      obtain ⟨db⟩ := ihb
      exact ⟨.let₁ da db⟩
  | unit => rw [hT.unit]; exact ⟨.unit⟩
  | pair _ _ iha ihb =>
      obtain ⟨da⟩ := iha
      obtain ⟨db⟩ := ihb
      rw [hT.product]
      exact ⟨.pair da db⟩
  | let₂ _ _ iha ihc =>
      obtain ⟨da⟩ := iha
      obtain ⟨dc⟩ := ihc
      rw [hT.product] at da
      exact ⟨.let₂ da dc⟩
  | inl _ ih =>
      obtain ⟨d⟩ := ih
      rw [hT.coprod]
      exact ⟨.inl d⟩
  | inr _ ih =>
      obtain ⟨d⟩ := ih
      rw [hT.coprod]
      exact ⟨.inr d⟩
  | case _ _ _ ihe ihl ihr =>
      obtain ⟨de⟩ := ihe
      obtain ⟨dl⟩ := ihl
      obtain ⟨dr⟩ := ihr
      rw [hT.coprod] at de
      exact ⟨.case de dl dr⟩
  | abort _ ih =>
      obtain ⟨d⟩ := ih
      rw [hT.empty] at d
      exact ⟨.abort d⟩
  | iter _ _ iha ihb =>
      obtain ⟨da⟩ := iha
      obtain ⟨db⟩ := ihb
      rw [hT.coprod] at db
      exact ⟨.iter da db⟩

theorem hasType_ofThesis (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    {Γ : Silmaril.Thesis.LambdaIter.Ctx ν τ} {n : Nat}
    {β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n} {t : TTm ν Φ n} {A : τ}
    (h : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType Φ Γ β t A) :
    Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ (Ctx.ofThesis Γ)
      (BoundCtx.ofThesis β) (ofThesis t) A := by
  induction h with
  | fv hx => exact .fv (by rw [Ctx.lookup_ofThesis]; exact hx)
  | bv => rw [← BoundCtx.get_ofThesis]; exact .bv
  | op _ ih =>
      rw [← hI.src] at ih
      rw [← hI.trg]
      exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => rw [← hT.unit]; exact .unit
  | pair _ _ iha ihb => rw [← hT.product]; exact .pair iha ihb
  | let₂ _ _ iha ihc => rw [← hT.product] at iha; exact .let₂ iha ihc
  | inl _ ih => rw [← hT.coprod]; exact .inl ih
  | inr _ ih => rw [← hT.coprod]; exact .inr ih
  | case _ _ _ ihe ihl ihr => rw [← hT.coprod] at ihe; exact .case ihe ihl ihr
  | abort _ ih => rw [← hT.empty] at ih; exact .abort ih
  | iter _ _ iha ihb => rw [← hT.coprod] at ihb; exact .iter iha ihb

/-- **Typing bridge.** Legacy exact typing is inhabitation of thesis exact typing of the
translated term in the translated contexts. -/
theorem hasType_iff (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    {Γ : Silmaril.Isotope.Ctx ν τ} {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {t : LTm ν Φ n} {A : τ} :
    Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ Γ β t A ↔
      Nonempty (Silmaril.Thesis.LambdaIter.LocallyNameless.HasType Φ (Ctx.toThesis Γ)
        (BoundCtx.toThesis β) (toThesis t) A) :=
  ⟨hasType_toThesis hT hI, fun ⟨d⟩ => by
    simpa only [Ctx.ofThesis_toThesis, BoundCtx.ofThesis_toThesis, ofThesis_toThesis] using
      hasType_ofThesis hT hI d⟩

/-- The typing bridge read from the thesis side. -/
theorem hasType_iff' (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    {Γ : Silmaril.Thesis.LambdaIter.Ctx ν τ} {n : Nat}
    {β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n} {t : TTm ν Φ n} {A : τ} :
    Nonempty (Silmaril.Thesis.LambdaIter.LocallyNameless.HasType Φ Γ β t A) ↔
      Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ (Ctx.ofThesis Γ)
        (BoundCtx.ofThesis β) (ofThesis t) A :=
  ⟨fun ⟨d⟩ => hasType_ofThesis hT hI d, fun h => by
    simpa only [Ctx.toThesis_ofThesis, BoundCtx.toThesis_ofThesis, toThesis_ofThesis] using
      hasType_toThesis hT hI h⟩

end Silmaril.Proofs.SSA.Isotope.Bridge
