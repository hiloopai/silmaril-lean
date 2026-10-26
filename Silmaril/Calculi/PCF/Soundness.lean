module

public import Silmaril.Calculi.PCF.Denotation
public import Silmaril.Calculi.PCF.SmallStep

/-! # Soundness

§6.4 of the notes. If `t ⇓ v` then `⟦t⟧ = ⟦v⟧` (Theorem 28), for PCF and for
PCF+`por`. The notes prove the Fun and Fix cases and leave the others as
exercises; all rules are covered here. Every transition also preserves
denotations. As a consequence, a program of ground type whose denotation is
`⊥` diverges (Proposition 29).
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

variable {p : Bool} {τ : Ty}

theorem predPart_map_succ (x : Part ℕ) : Flat.lift predPart (Flat.map Nat.succ x) = x := by
  rcases Part.eq_none_or_eq_some x with rfl | ⟨n, rfl⟩
  · simp
  · simp [predPart]

/-- Closed values of ground type denote defined elements. -/
theorem denote_value_nat {v : Closed p .nat} (hv : Value v) (ρ : (model p).Env []) :
    ∃ n : ℕ, denote v ρ = (Part.some n : Part ℕ) := by
  obtain ⟨n, rfl⟩ := hv.eq_num
  exact ⟨n, denote_num _ n⟩

theorem denote_value_bool {v : Closed p .bool} (hv : Value v) (ρ : (model p).Env []) :
    ∃ b : Bool, denote v ρ = (Part.some b : Part Bool) := by
  obtain ⟨b, rfl⟩ := hv.eq_bool
  exact ⟨b, denote_bool _ b⟩

/-- Theorem 28 (soundness): if `t ⇓ v` then `⟦t⟧ = ⟦v⟧`. -/
theorem Eval.denote_eq {t v : Closed p τ} (h : t ⇓ v) : denote t = denote v := by
  induction h with
  | val => rfl
  | succ _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_succ, ih]
      rfl
  | pred _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_pred, ih, denote_succ, predPart_map_succ]
  | isZeroZ _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_isZero, ih, denote_zero, Flat.map_some]
      rfl
  | isZeroS h ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      have hv : Value _ := h.value.succ_inv
      obtain ⟨n, hn⟩ := denote_value_nat hv ρ
      rw [denote_op_isZero, ih, denote_succ]
      erw [hn]
      rw [Flat.map_some, Flat.map_some]
      rfl
  | iteT _ _ ihb iht =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_ite, ihb, denote_tt, condFun_true, iht]
  | iteF _ _ ihb iht =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_ite, ihb, denote_ff, condFun_false, iht]
  | app _ _ iht ihs =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [← ihs]
      change Model.app (denote _ ρ) (denote _ ρ) = _
      rw [iht, Model.denote_subst1]
      rfl
  | fix _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [← ih, denote_op_fix, ← fix_eq]
      rfl
  | porL _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_por, ih, denote_tt, porFun_true_left]
  | porR _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_por, ih, denote_tt, porFun_true_right]
  | porF _ _ ih ih' =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_por, ih, ih', denote_ff, porFun_false_false]

/-- Transitions preserve denotations. -/
theorem Step.denote_eq {t t' : Closed p τ} (h : Step t t') : denote t = denote t' := by
  induction h with
  | succ _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_succ, ih]
      rfl
  | pred _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_pred, ih]
      rfl
  | isZero _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_isZero, ih]
      rfl
  | predSucc e _ =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_pred, e, denote_succ, predPart_map_succ]
  | isZeroZero e =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_isZero, e, denote_zero, Flat.map_some]
      rfl
  | isZeroSucc e hv =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      obtain ⟨n, hn⟩ := denote_value_nat hv ρ
      rw [denote_op_isZero, e, denote_succ, hn, Flat.map_some, Flat.map_some]
      rfl
  | ite _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_ite, denote_op_ite, ih]
      rfl
  | iteT e =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_ite, e, denote_tt, condFun_true]
  | iteF e =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_ite, e, denote_ff, condFun_false]
  | app _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [Model.denote_app, Model.denote_app]
      exact congrArg (fun f => Model.app (M := model _) (f ρ) _) ih
  | beta =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [Model.denote_app, Model.denote_subst1]
      rfl
  | fix =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_fix, ← fix_eq]
      rfl
  | porL _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_por, denote_op_por, ih]
      rfl
  | porR _ ih =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_por, denote_op_por, ih]
      rfl
  | porTL e =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_por, e, denote_tt, porFun_true_left]
  | porTR e =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_por, e, denote_tt, porFun_true_right]
  | porFF e e' =>
      refine ContinuousHom.ext _ _ fun ρ => ?_
      rw [denote_op_por, e, e', denote_ff, porFun_false_false]

/-- Proposition 29: a program of ground type denoting `⊥` diverges. -/
theorem diverges_of_denote_eq_bot {γ : Ty} (hγ : γ.IsGround) {t : Closed p γ}
    (h : denote t Tuple.nil = (⊥ : (model p).ty γ)) : Diverges t := by
  intro v hv
  rw [hv.denote_eq] at h
  match γ, hγ, v, hv.value with
  | .base .nat, _, _, hv' =>
      obtain ⟨n, hn⟩ := denote_value_nat hv' Tuple.nil
      exact Part.some_ne_none n (hn.symm.trans h)
  | .base .bool, _, _, hv' =>
      obtain ⟨b, hb⟩ := denote_value_bool hv' Tuple.nil
      exact Part.some_ne_none b (hb.symm.trans h)

end Silmaril.Calculi.PCF
