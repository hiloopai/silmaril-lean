module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlNaturality
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ResourceNaturality

/-! # Normalized iteration equations and pure uniformity -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.IterModel

open CategoryTheory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- Directed uniformity in the signature's literal sum types. -/
theorem uniformity (p : Polarity) {e η : ε} {A B D : τ}
    {h : M.Hom A B} {f : M.Hom B (coprod D B)} {g : M.Hom A (coprod D A)}
    (he : EffectSystem.iterable e) (hm : EffectSystem.moves p η e)
    (hh : M.hasEffect η h) (hf : M.hasEffect e f)
    (hs : p.orient M.le (M.compose h f)
      (M.compose g (M.desc (M.inl D B) (M.compose h (M.inr D B))))) :
    p.orient M.le (M.compose h (M.iterate f)) (M.iterate g) := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  have hs' : p.orient M.le
      (h ≫ (f ≫ eqToHom (M.sum_obj D B).symm))
      ((g ≫ eqToHom (M.sum_obj D A).symm) ≫ M.coproducts.map (𝟙 D) h) := by
    have hpost := M.toSeqData.orient_compose_right p hs (eqToHom (M.sum_obj D B).symm)
    simpa [SeqData.le, SeqData.compose, CaseData.desc, CaseData.inl, CaseData.inr,
      ChosenCoproducts.map, ChosenCoproducts.desc_compose, Category.assoc] using hpost
  exact M.iterLaws.uniformity p he hm hh
    (M.effects.comp hf (M.toSeqData.eqToHom_effect _ _)) hs'

/-- An exact simulation by a pure arrow commutes with iteration. Neither loop
body needs a special effect bound: the iterable top effect suffices. -/
theorem pure_uniformity {A B D : τ} {h : M.Hom A B}
    {f : M.Hom B (coprod D B)} {g : M.Hom A (coprod D A)}
    (hh : M.hasEffect ⊥ h)
    (hs : M.compose h f =
      M.compose g (M.desc (M.inl D B) (M.compose h (M.inr D B)))) :
    M.compose h (M.iterate f) = M.iterate g := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  apply le_antisymm
  · exact M.uniformity .positive EffectSystem.iterable_top
      (EffectSystem.pure_moves .positive ⊤) hh (M.effects.top f) (le_of_eq hs)
  · exact M.uniformity .negative EffectSystem.iterable_top
      (EffectSystem.pure_moves .negative ⊤) hh (M.effects.top f) (le_of_eq hs.symm)

end Silmaril.Isotope.Refinement.Models.IterModel
