module

public import Silmaril.Calculi.PCF.Partrec

/-! # Finite bounds on evaluation derivations

`EvalWithin k t v` bounds the height of a big-step derivation. Every evaluation
has such a bound. The bound supports induction through recursive calls after
inverting several applications and a fixed-point unfolding.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF

open TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

inductive EvalWithin : ℕ → {p : Bool} → {τ : Ty} → Closed p τ → Closed p τ → Prop
  | val {k p τ} {v : Closed p τ} : Value v → EvalWithin (k + 1) v v
  | succ {k p} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      EvalWithin k args.head v → EvalWithin (k + 1) (.op .succ args) (.succ v)
  | pred {k p} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      EvalWithin k args.head (.succ v) → EvalWithin (k + 1) (.op .pred args) v
  | isZeroZ {k p} {args : Tuple (Closed p) [.nat]} :
      EvalWithin k args.head .zero → EvalWithin (k + 1) (.op .isZero args) .tt
  | isZeroS {k p} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      EvalWithin k args.head (.succ v) → EvalWithin (k + 1) (.op .isZero args) .ff
  | iteT {k p τ} {args : Tuple (Closed p) [.bool, τ, τ]} {v : Closed p τ} :
      EvalWithin k args.head .tt → EvalWithin k args.tail.head v →
      EvalWithin (k + 1) (.op (.ite τ) args) v
  | iteF {k p τ} {args : Tuple (Closed p) [.bool, τ, τ]} {v : Closed p τ} :
      EvalWithin k args.head .ff → EvalWithin k args.tail.tail.head v →
      EvalWithin (k + 1) (.op (.ite τ) args) v
  | app {k p σ τ} {t : Closed p (σ ⤳ τ)} {b : Term p [σ] τ} {u : Closed p σ}
      {v : Closed p τ} : EvalWithin k t (.lam b) → EvalWithin k (b.subst1 u) v →
      EvalWithin (k + 1) (.app t u) v
  | fix {k p τ} {args : Tuple (Closed p) [τ ⤳ τ]} {v : Closed p τ} :
      EvalWithin k (.app args.head (.op (.fix τ) args)) v →
      EvalWithin (k + 1) (.op (.fix τ) args) v
  | porL {k} {args : Tuple (Closed true) [.bool, .bool]} :
      EvalWithin k args.head .tt → EvalWithin (k + 1) (.op .por args) .tt
  | porR {k} {args : Tuple (Closed true) [.bool, .bool]} :
      EvalWithin k args.tail.head .tt → EvalWithin (k + 1) (.op .por args) .tt
  | porF {k} {args : Tuple (Closed true) [.bool, .bool]} :
      EvalWithin k args.head .ff → EvalWithin k args.tail.head .ff →
      EvalWithin (k + 1) (.op .por args) .ff

namespace EvalWithin

variable {k l : ℕ} {p : Bool} {σ τ : Ty} {t v : Closed p τ}

theorem toEval (h : EvalWithin k t v) : t ⇓ v := by
  induction h with
  | val hv => exact .val hv
  | succ _ ih => exact .succ ih
  | pred _ ih => exact .pred ih
  | isZeroZ _ ih => exact .isZeroZ ih
  | isZeroS _ ih => exact .isZeroS ih
  | iteT _ _ ih ih' => exact .iteT ih ih'
  | iteF _ _ ih ih' => exact .iteF ih ih'
  | app _ _ ih ih' => exact .app ih ih'
  | fix _ ih => exact .fix ih
  | porL _ ih => exact .porL ih
  | porR _ ih => exact .porR ih
  | porF _ _ ih ih' => exact .porF ih ih'

theorem step (h : EvalWithin k t v) : EvalWithin (k + 1) t v := by
  induction h with
  | val hv => exact .val hv
  | succ _ ih => exact .succ ih
  | pred _ ih => exact .pred ih
  | isZeroZ _ ih => exact .isZeroZ ih
  | isZeroS _ ih => exact .isZeroS ih
  | iteT _ _ ih ih' => exact .iteT ih ih'
  | iteF _ _ ih ih' => exact .iteF ih ih'
  | app _ _ ih ih' => exact .app ih ih'
  | fix _ ih => exact .fix ih
  | porL _ ih => exact .porL ih
  | porR _ ih => exact .porR ih
  | porF _ _ ih ih' => exact .porF ih ih'

theorem mono (h : EvalWithin k t v) (hkl : k ≤ l) : EvalWithin l t v := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact ih.step

theorem beta_inv {b : Term p [σ] τ} {u : Closed p σ}
    (h : EvalWithin k (.app (.lam b) u) v) :
    ∃ l < k, EvalWithin l (b.subst1 u) v := by
  cases h with
  | val hv => cases hv
  | app hf hb =>
      cases Eval.of_value (.lam _) hf.toEval
      exact ⟨_, Nat.lt_succ_self _, hb⟩

theorem ite_inv {b : Closed p .bool} {t t' v : Closed p τ}
    (h : EvalWithin k (Term.ite b t t') v) :
    ∃ l < k, (EvalWithin l b .tt ∧ EvalWithin l t v) ∨
      (EvalWithin l b .ff ∧ EvalWithin l t' v) := by
  cases h with
  | val hv => cases hv
  | iteT hb ht => exact ⟨_, Nat.lt_succ_self _, Or.inl ⟨hb, ht⟩⟩
  | iteF hb ht => exact ⟨_, Nat.lt_succ_self _, Or.inr ⟨hb, ht⟩⟩

end EvalWithin

theorem Eval.exists_within {p : Bool} {τ : Ty} {t v : Closed p τ} (h : t ⇓ v) :
    ∃ k, EvalWithin k t v := by
  induction h with
  | val hv => exact ⟨1, .val hv⟩
  | succ _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, .succ hk⟩
  | pred _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, .pred hk⟩
  | isZeroZ _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, .isZeroZ hk⟩
  | isZeroS _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, .isZeroS hk⟩
  | fix _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, .fix hk⟩
  | porL _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, .porL hk⟩
  | porR _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, .porR hk⟩
  | iteT _ _ ih ih' =>
      obtain ⟨k, hk⟩ := ih; obtain ⟨l, hl⟩ := ih'
      exact ⟨max k l + 1, .iteT (hk.mono (le_max_left ..)) (hl.mono (le_max_right ..))⟩
  | iteF _ _ ih ih' =>
      obtain ⟨k, hk⟩ := ih; obtain ⟨l, hl⟩ := ih'
      exact ⟨max k l + 1, .iteF (hk.mono (le_max_left ..)) (hl.mono (le_max_right ..))⟩
  | app _ _ ih ih' =>
      obtain ⟨k, hk⟩ := ih; obtain ⟨l, hl⟩ := ih'
      exact ⟨max k l + 1, .app (hk.mono (le_max_left ..)) (hl.mono (le_max_right ..))⟩
  | porF _ _ ih ih' =>
      obtain ⟨k, hk⟩ := ih; obtain ⟨l, hl⟩ := ih'
      exact ⟨max k l + 1, .porF (hk.mono (le_max_left ..)) (hl.mono (le_max_right ..))⟩

/-- Unfoldings that do not increase the height needed for evaluation. -/
def ContractsWithin {p : Bool} {τ : Ty} (t t' : Closed p τ) : Prop :=
  ∀ {k v}, EvalWithin k t' v → EvalWithin k t v

namespace ContractsWithin

variable {p : Bool} {σ τ : Ty}

theorem beta (b : Term p [σ] τ) (u : Closed p σ) :
    ContractsWithin (b.subst1 u) (.app (.lam b) u) := by
  intro k v h
  obtain ⟨l, hl, hb⟩ := h.beta_inv
  exact hb.mono hl.le

theorem fix (t : Closed p (τ ⤳ τ)) :
    ContractsWithin (.app t (Term.fix t)) (Term.fix t) := by
  intro k v h
  cases h with
  | val hv => cases hv
  | fix h => exact h.step

theorem app {t t' : Closed p (σ ⤳ τ)} (h : ContractsWithin t t') (u : Closed p σ) :
    ContractsWithin (.app t u) (.app t' u) := by
  intro k v he
  cases he with
  | val hv => cases hv
  | app hf hb => exact .app (h hf) hb

theorem apps : {n : ℕ} → {t t' : Closed p (Ty.arrows n)} → ContractsWithin t t' →
    (us : Fin n → Closed p .nat) → ContractsWithin (Term.apps t us) (Term.apps t' us)
  | 0, _, _, h, _ => h
  | _ + 1, _, _, h, us => apps (h.app (us 0)) (Fin.tail us)

end ContractsWithin

namespace EvalWithin

variable {p : Bool}

theorem apps_lams_inv : {Γ : Ctx Base} → {n : ℕ} →
    (b : Term p (ctxN n Γ) .nat) → (s : Subst (sig p) Γ []) →
    (us : Fin n → Closed p .nat) → {k : ℕ} → {v : Closed p .nat} →
    EvalWithin k (Term.apps ((Term.lams n b).subst s) us) v →
    ∃ l ≤ k, EvalWithin l (b.subst (Subst.extendN n s us)) v ∧ (0 < n → l < k)
  | _, 0, _, _, _, k, _, h => ⟨k, le_rfl, h, by omega⟩
  | Γ, n + 1, b, s, us, k, v, h => by
      have h' := ContractsWithin.apps (ContractsWithin.beta _ (us 0)) (Fin.tail us) h
      rw [TypedLambda.Term.subst_lift_subst1] at h'
      obtain ⟨l, hl, hb, hlt⟩ := apps_lams_inv (Γ := Ty.nat :: Γ) b (us 0 ::ₜ s)
        (Fin.tail us) h'
      cases n with
      | zero =>
          obtain ⟨l', hl', hb'⟩ := h.beta_inv
          refine ⟨l', hl'.le, ?_, fun _ => hl'⟩
          change EvalWithin l' ((b.subst s.lift).subst1 (us 0)) v at hb'
          exact (TypedLambda.Term.subst_lift_subst1 s b (us 0)) ▸ hb'
      | succ n => exact ⟨l, hl, hb, fun _ => hlt (by omega)⟩

theorem apps_fix_lams_inv {n : ℕ} (hn : 0 < n)
    (b : Term p (ctxN n [Ty.arrows n]) .nat) (us : Fin n → Closed p .nat)
    {k : ℕ} {v : Closed p .nat}
    (h : EvalWithin k (Term.apps (Term.fix (.lam (Term.lams n b))) us) v) :
    ∃ l < k, EvalWithin l
      (b.subst (Subst.extendN n (Subst.single (Term.fix (.lam (Term.lams n b)))) us)) v := by
  have h' := ContractsWithin.apps (ContractsWithin.fix _) us h
  have h'' := ContractsWithin.apps (ContractsWithin.beta _ _) us h'
  obtain ⟨l, _, hb, hlt⟩ := apps_lams_inv b _ us h''
  exact ⟨l, hlt hn, hb⟩

end EvalWithin
end Silmaril.Calculi.PCF
