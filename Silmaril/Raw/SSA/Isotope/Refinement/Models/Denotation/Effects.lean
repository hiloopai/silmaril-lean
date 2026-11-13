module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Typing

/-! # Effect preservation of categorical interpretation

Every native typing derivation denotes an arrow of its stated effect. The
control-effect interface only factors the proof across the three fragments;
its witnesses are constructed below from the actual model axioms.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace CaseData
variable (M : CaseData.{u,v,w,r} τ Φ ε)

theorem inl_pure (A B : τ) : M.toSeqData.hasEffect ⊥ (M.inl A B) := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  exact M.effects.comp (M.caseLaws.inl A B) (M.toSeqData.eqToHom_effect _ _)

theorem inr_pure (A B : τ) : M.toSeqData.hasEffect ⊥ (M.inr A B) := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  exact M.effects.comp (M.caseLaws.inr A B) (M.toSeqData.eqToHom_effect _ _)

theorem desc_effect {e : ε} {A B D : τ} {f : M.toSeqData.Hom A D}
    {g : M.toSeqData.Hom B D} (hf : M.toSeqData.hasEffect e f)
    (hg : M.toSeqData.hasEffect e g) : M.toSeqData.hasEffect e (M.desc f g) := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  exact M.effects.comp (M.toSeqData.eqToHom_effect _ _) (M.caseLaws.desc hf hg)

theorem abort_pure (A : τ) : M.toSeqData.hasEffect ⊥ (M.abort A) := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  exact M.effects.comp (M.toSeqData.eqToHom_effect _ _) (M.caseLaws.initial A)

theorem distribute_pure (D A B : τ) : M.toSeqData.hasEffect ⊥ (M.distribute D A B) := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  let := M.caseLaws.distributor_isIso D A B
  exact M.effects.comp (M.toSeqData.eqToHom_effect _ _)
    (M.effects.comp (M.caseLaws.distributor_inv D A B) (M.toSeqData.eqToHom_effect _ _))
end CaseData

namespace IterModel
variable (M : IterModel.{u,v,w,r} τ Φ ε)

theorem iterate_effect {e : ε} {A B : τ} {f : M.toSeqData.Hom A (coprod B A)}
    (he : EffectSystem.iterable e) (hf : M.toSeqData.hasEffect e f) :
    M.toSeqData.hasEffect e (M.iterate f) := by
  let := M.toSeqData.category
  let := M.toSeqData.homOrder
  let := M.toSeqData.premonoidal
  let := M.toSeqData.symmetric
  exact M.iterLaws.effect he (M.effects.comp hf (M.toSeqData.eqToHom_effect _ _))
end IterModel

namespace Denotation
variable {M : SeqData.{u,v,w,r} τ Φ ε} {F : Fragment}

/-- Effect bounds for the optional control operations. -/
structure ControlEffects (K : ControlData M F) : Prop where
  inl (h : F.HasCase) (A B : τ) : M.hasEffect ⊥ (K.inl h A B)
  inr (h : F.HasCase) (A B : τ) : M.hasEffect ⊥ (K.inr h A B)
  desc (h : F.HasCase) {e : ε} {A B D : τ} {f : M.Hom A D} {g : M.Hom B D} :
    M.hasEffect e f → M.hasEffect e g → M.hasEffect e (K.desc h f g)
  abort (h : F.HasCase) (A : τ) : M.hasEffect ⊥ (K.abort h A)
  distribute (h : F.HasCase) (D A B : τ) : M.hasEffect ⊥ (K.distribute h D A B)
  iterate (h : F.HasIter) {e : ε} {A B : τ} {f : M.Hom A (coprod B A)} :
    EffectSystem.iterable e → M.hasEffect e f → M.hasEffect e (K.iterate h f)

namespace ControlEffects

theorem seq (M : SeqModel.{u,v,w,r} τ Φ ε) : ControlEffects (ControlData.seq M) where
  inl h := False.elim h
  inr h := False.elim h
  desc h := False.elim h
  abort h := False.elim h
  distribute h := False.elim h
  iterate h := False.elim h

theorem ofCase (M : CaseData.{u,v,w,r} τ Φ ε) (F : Fragment)
    (it : F.HasIter → ∀ {A B : τ}, M.toSeqData.Hom A (coprod B A) → M.toSeqData.Hom A B)
    (he : ∀ h {e : ε} {A B : τ} {f : M.toSeqData.Hom A (coprod B A)},
      EffectSystem.iterable e → M.toSeqData.hasEffect e f → M.toSeqData.hasEffect e (it h f)) :
    ControlEffects (ControlData.ofCase M F it) where
  inl _ := M.inl_pure
  inr _ := M.inr_pure
  desc _ := M.desc_effect
  abort _ := M.abort_pure
  distribute _ := M.distribute_pure
  iterate := he

theorem case (M : CaseModel.{u,v,w,r} τ Φ ε) : ControlEffects (ControlData.case M) :=
  ofCase M.toCaseData .case (fun h => False.elim h) (fun h => False.elim h)

theorem iter (M : IterModel.{u,v,w,r} τ Φ ε) : ControlEffects (ControlData.iter M) :=
  ofCase M.toCaseData .iter (fun _ => M.iterate) (fun _ => M.iterate_effect)

variable {K : ControlData M F} (E : ControlEffects K)

include E in
theorem iterateWithContext {e : ε} (he : EffectSystem.iterable e) (h : F.HasIter) (D : τ)
    (hc : Quantity.relevant ≤ quantity D) (hd : Quantity.affine ≤ quantity D)
    {A B : τ} {body : M.Hom (product D A) (coprod B A)} (hb : M.hasEffect e body) :
    M.hasEffect e (K.iterateWithContext h D hc hd body) := by
  apply E.iterate h he
  apply M.compose_effect (M.effect_mono bot_le (M.right_effect _ (M.copy_pure D hc)))
  apply M.compose_effect (M.effect_mono bot_le (M.associator_pure _ _ _))
  apply M.compose_effect (M.left_effect _ hb)
  apply M.compose_effect (M.effect_mono bot_le (E.distribute _ _ _ _))
  apply E.desc
  · apply M.compose_effect (M.effect_mono bot_le (M.right_effect _ (M.discard_pure D hd)))
    exact M.compose_effect (M.effect_mono bot_le (M.leftUnitor_pure _))
      (M.effect_mono bot_le (E.inl _ _ _))
  · exact M.effect_mono bot_le (E.inr _ _ _)

end ControlEffects

/-- Native typing implies the denotation belongs to the declared wide effect
subcategory, including retained environments in iteration. -/
theorem denote_effect (K : ControlData M F) (E : ControlEffects K)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) : M.hasEffect e (denote M K h) := by
  induction h with
  | var i h => exact M.effect_mono bot_le (variable_pure M i h)
  | op hf h ih => exact M.compose_effect ih (M.effect_mono hf (M.instruction_effect _))
  | let₁ s h k ih ik =>
    exact M.compose_effect (M.effect_mono bot_le (split_pure M s))
      (M.compose_effect (M.left_effect _ ih) ik)
  | unit h => exact M.effect_mono bot_le (discard_pure M h)
  | pair s h k ih ik =>
    exact M.compose_effect (M.effect_mono bot_le (split_pure M s)) (M.tensor_effect ih ik)
  | let₂ s h k ih ik =>
    exact M.compose_effect (M.effect_mono bot_le (split_pure M s))
      (M.compose_effect (M.left_effect _ ih)
        (M.compose_effect (M.effect_mono bot_le (M.associatorInv_pure _ _ _)) ik))
  | inl f h ih => exact M.compose_effect ih (M.effect_mono bot_le (E.inl f _ _))
  | inr f h ih => exact M.compose_effect ih (M.effect_mono bot_le (E.inr f _ _))
  | case f s h l r ih il ir =>
    exact M.compose_effect (M.effect_mono bot_le (split_pure M s))
      (M.compose_effect (M.left_effect _ ih)
        (M.compose_effect (M.effect_mono bot_le (E.distribute f _ _ _)) (E.desc f il ir)))
  | abort f h ih => exact M.compose_effect ih (M.effect_mono bot_le (E.abort f _))
  | iter f s u it h k ih ik =>
    exact M.compose_effect (M.effect_mono bot_le (split_pure M s))
      (M.compose_effect (M.left_effect _ ih) (E.iterateWithContext it f _ _ _ ik))

theorem denoteSeq_effect (M : SeqModel.{u,v,w,r} τ Φ ε)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType .seq Γ e t A) : M.toSeqData.hasEffect e (denoteSeq M h) :=
  denote_effect _ (ControlEffects.seq M) h

theorem denoteCase_effect (M : CaseModel.{u,v,w,r} τ Φ ε)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType .case Γ e t A) : M.toSeqData.hasEffect e (denoteCase M h) :=
  denote_effect _ (ControlEffects.case M) h

theorem denoteIter_effect (M : IterModel.{u,v,w,r} τ Φ ε)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType .iter Γ e t A) : M.toSeqData.hasEffect e (denoteIter M h) :=
  denote_effect _ (ControlEffects.iter M) h

end Denotation
end Silmaril.Isotope.Refinement.Models
