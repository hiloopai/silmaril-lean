module

public import Silmaril.Calculi.PCF.BigStep
public import Cslib.Foundations.Relation.Termination
public import Cslib.Foundations.Relation.Attr
public import Cslib.Foundations.Relation.Confluence

/-! # Transitions

The small-step transition relation `t ⇝ t'` of Figure 4 of the notes
(Remark 7), extended to PCF+`por` as asked by Exercise 22. The relation is
registered with CSLib's `reduction_sys` attribute, so `t ⭢ t'` is a step and
`t ↠ t'` is its reflexive-transitive closure (`Relation.ReflTransGen`).

For parallel or, either argument may take a step, and a result is produced as
soon as one argument is `true` or both are `false`. The main theorem is
Remark 7 for both languages: `t ⇓ v ↔ t ↠ v` for every value `v`
(`eval_iff_steps`). Values are CSLib normal forms. Transitions of PCF are
deterministic, while those of PCF+`por` are not.

As for evaluation, rules about operators quantify over the argument tuple;
nested patterns such as `pred(succ(v))` become equations on the arguments.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Figure 4, with transitions for parallel or (Exercise 22). -/
@[reduction_sys]
inductive Step : {p : Bool} → {τ : Ty} → Closed p τ → Closed p τ → Prop
  /-- Reduce the argument of `succ`. -/
  | succ {p : Bool} {args : Tuple (Closed p) [.nat]} {t' : Closed p .nat} :
      Step args.head t' → Step (.op .succ args) (.succ t')
  /-- Reduce the argument of `pred`. -/
  | pred {p : Bool} {args : Tuple (Closed p) [.nat]} {t' : Closed p .nat} :
      Step args.head t' → Step (.op .pred args) (.pred t')
  /-- Reduce the argument of `zero?`. -/
  | isZero {p : Bool} {args : Tuple (Closed p) [.nat]} {t' : Closed p .nat} :
      Step args.head t' → Step (.op .isZero args) (.isZero t')
  /-- `pred(succ(v)) ⇝ v`. -/
  | predSucc {p : Bool} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      args.head = .succ v → Value v → Step (.op .pred args) v
  /-- `zero?(𝟶) ⇝ true`. -/
  | isZeroZero {p : Bool} {args : Tuple (Closed p) [.nat]} :
      args.head = .zero → Step (.op .isZero args) .tt
  /-- `zero?(succ(v)) ⇝ false`. -/
  | isZeroSucc {p : Bool} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      args.head = .succ v → Value v → Step (.op .isZero args) .ff
  /-- Reduce the condition of `if`. -/
  | ite {p : Bool} {τ : Ty} {args : Tuple (Closed p) [.bool, τ, τ]} {b' : Closed p .bool} :
      Step args.head b' → Step (.op (.ite τ) args) (.op (.ite τ) (b' ::ₜ args.tail))
  /-- `if true then t₁ else t₂ ⇝ t₁`. -/
  | iteT {p : Bool} {τ : Ty} {args : Tuple (Closed p) [.bool, τ, τ]} :
      args.head = .tt → Step (.op (.ite τ) args) args.tail.head
  /-- `if false then t₁ else t₂ ⇝ t₂`. -/
  | iteF {p : Bool} {τ : Ty} {args : Tuple (Closed p) [.bool, τ, τ]} :
      args.head = .ff → Step (.op (.ite τ) args) args.tail.tail.head
  /-- Reduce the function of an application. -/
  | app {p : Bool} {σ τ : Ty} {t t' : Closed p (σ ⤳ τ)} {u : Closed p σ} :
      Step t t' → Step (.app t u) (.app t' u)
  /-- `(fun x:σ. t) u ⇝ t[u/x]`. -/
  | beta {p : Bool} {σ τ : Ty} {t : Term p [σ] τ} {u : Closed p σ} :
      Step (.app (.lam t) u) (t.subst1 u)
  /-- `fix(t) ⇝ t (fix(t))`. -/
  | fix {p : Bool} {τ : Ty} {args : Tuple (Closed p) [τ ⤳ τ]} :
      Step (.op (.fix τ) args) (.app args.head (.op (.fix τ) args))
  /-- Reduce the left argument of `por`. -/
  | porL {args : Tuple (Closed true) [.bool, .bool]} {t' : Closed true .bool} :
      Step args.head t' → Step (.op .por args) (.op .por (t' ::ₜ args.tail))
  /-- Reduce the right argument of `por`. -/
  | porR {args : Tuple (Closed true) [.bool, .bool]} {u' : Closed true .bool} :
      Step args.tail.head u' → Step (.op .por args) (.op .por (args.head ::ₜ .single u'))
  /-- `por(true, u) ⇝ true`. -/
  | porTL {args : Tuple (Closed true) [.bool, .bool]} :
      args.head = .tt → Step (.op .por args) .tt
  /-- `por(t, true) ⇝ true`. -/
  | porTR {args : Tuple (Closed true) [.bool, .bool]} :
      args.tail.head = .tt → Step (.op .por args) .tt
  /-- `por(false, false) ⇝ false`. -/
  | porFF {args : Tuple (Closed true) [.bool, .bool]} :
      args.head = .ff → args.tail.head = .ff → Step (.op .por args) .ff

namespace Step

variable {p : Bool} {τ : Ty}

/-- Values do not reduce: they are CSLib normal forms. -/
theorem value_normal {v : Closed p τ} (hv : Value v) : Relation.Normal Step v := by
  rintro ⟨t, h⟩
  induction hv with
  | @succ args _ ih => cases h with | succ h => exact ih _ h
  | _ => cases h

theorem not_of_value {v t : Closed p τ} (hv : Value v) (h : Step v t) : False :=
  value_normal hv ⟨t, h⟩

/-- Lift reductions of a subterm through a context. -/
theorem steps_lift {σ : Ty} (f : Closed p σ → Closed p τ)
    (hf : ∀ {a b}, Step a b → Step (f a) (f b)) {a b : Closed p σ}
    (h : Relation.ReflTransGen Step a b) : Relation.ReflTransGen Step (f a) (f b) :=
  Relation.ReflTransGen.lift f (fun _ _ h' => hf h') _ _ h

theorem steps_succ {a b : Closed p .nat} (h : Relation.ReflTransGen Step a b) :
    Relation.ReflTransGen Step (Term.succ a) (Term.succ b) :=
  steps_lift Term.succ (fun {a _} h => Step.succ (args := .single a) h) h

theorem steps_pred {a b : Closed p .nat} (h : Relation.ReflTransGen Step a b) :
    Relation.ReflTransGen Step (Term.pred a) (Term.pred b) :=
  steps_lift Term.pred (fun {a _} h => Step.pred (args := .single a) h) h

theorem steps_isZero {a b : Closed p .nat} (h : Relation.ReflTransGen Step a b) :
    Relation.ReflTransGen Step (Term.isZero a) (Term.isZero b) :=
  steps_lift Term.isZero (fun {a _} h => Step.isZero (args := .single a) h) h

/-- Remark 7 and Exercise 22, one direction: evaluation is reachable by
transitions. -/
theorem of_eval {t v : Closed p τ} (h : t ⇓ v) : Relation.ReflTransGen Step t v := by
  induction h with
  | val => exact .refl
  | @succ _ args _ _ ih =>
      rw [← Tuple.single_head args]
      exact steps_succ ih
  | @pred _ args _ h ih =>
      rw [← Tuple.single_head args]
      exact (steps_pred ih).tail
        (.predSucc rfl h.value.succ_inv)
  | @isZeroZ _ args _ ih =>
      rw [← Tuple.single_head args]
      exact (steps_isZero ih).tail (.isZeroZero rfl)
  | @isZeroS _ args _ h ih =>
      rw [← Tuple.single_head args]
      exact (steps_isZero ih).tail
        (.isZeroSucc rfl h.value.succ_inv)
  | @iteT _ τ args _ _ _ ihb iht =>
      rw [Tuple.eq_cons args]
      exact ((steps_lift (fun b => .op (.ite τ) (b ::ₜ args.tail)) (fun h => .ite h) ihb).tail
        (.iteT rfl)).trans iht
  | @iteF _ τ args _ _ _ ihb iht =>
      rw [Tuple.eq_cons args]
      exact ((steps_lift (fun b => .op (.ite τ) (b ::ₜ args.tail)) (fun h => .ite h) ihb).tail
        (.iteF rfl)).trans iht
  | @app _ _ _ _ _ u _ _ _ iht ihs =>
      exact ((steps_lift (fun t => .app t u) (fun h => .app h) iht).tail .beta).trans ihs
  | fix _ ih => exact .head .fix ih
  | @porL args _ ih =>
      rw [Tuple.eq_cons args]
      exact (steps_lift (fun t => .op .por (t ::ₜ args.tail)) (fun h => .porL h) ih).tail
        (.porTL rfl)
  | @porR args _ ih =>
      rw [Tuple.eta₂ args]
      exact (steps_lift (fun u => .op .por (args.head ::ₜ .single u)) (fun h => .porR h) ih).tail
        (.porTR rfl)
  | @porF args _ _ ihl ihr =>
      rw [Tuple.eta₂ args]
      exact ((steps_lift (fun t => .op .por (t ::ₜ .single args.tail.head))
        (fun h => .porL h) ihl).trans
        (steps_lift (fun u => .op .por (Term.ff ::ₜ .single u)) (fun h => .porR h) ihr)).tail
        (.porFF rfl rfl)

/-- Transitions preserve the result of evaluation backwards. -/
theorem eval_of_step {t t' v : Closed p τ} (hs : Step t t') (h : t' ⇓ v) : t ⇓ v := by
  induction hs with
  | succ _ ih =>
      cases h with
      | val hv => exact .succ (ih (.val hv.succ_inv))
      | succ h => exact .succ (ih h)
  | pred _ ih =>
      cases h with
      | val hv => cases hv
      | pred h => exact .pred (ih h)
  | isZero _ ih =>
      cases h with
      | val hv => cases hv
      | isZeroZ h => exact .isZeroZ (ih h)
      | isZeroS h => exact .isZeroS (ih h)
  | predSucc e hv =>
      cases Eval.of_value hv h
      exact .pred (by rw [e]; exact .val hv.succ')
  | isZeroZero e =>
      cases Eval.of_value .tt h
      exact .isZeroZ (by rw [e]; exact .val .zero)
  | isZeroSucc e hv =>
      cases Eval.of_value .ff h
      exact .isZeroS (by rw [e]; exact .val hv.succ')
  | ite _ ih =>
      cases h with
      | val hv => cases hv
      | iteT hb ht => exact .iteT (ih hb) ht
      | iteF hb ht => exact .iteF (ih hb) ht
  | iteT e => exact .iteT (by rw [e]; exact .val .tt) h
  | iteF e => exact .iteF (by rw [e]; exact .val .ff) h
  | app _ ih =>
      cases h with
      | val hv => cases hv
      | app ht hs => exact .app (ih ht) hs
  | beta => exact .app (.val (.lam _)) h
  | fix => exact .fix h
  | porL _ ih =>
      cases h with
      | val hv => cases hv
      | porL h => exact .porL (ih h)
      | porR h => exact .porR h
      | porF h h' => exact .porF (ih h) h'
  | porR _ ih =>
      cases h with
      | val hv => cases hv
      | porL h => exact .porL h
      | porR h => exact .porR (ih h)
      | porF h h' => exact .porF h (ih h')
  | porTL e =>
      cases Eval.of_value .tt h
      exact .porL (by rw [e]; exact .val .tt)
  | porTR e =>
      cases Eval.of_value .tt h
      exact .porR (by rw [e]; exact .val .tt)
  | porFF e e' =>
      cases Eval.of_value .ff h
      exact .porF (by rw [e]; exact .val .ff) (by rw [e']; exact .val .ff)

/-- Remark 7 and Exercise 22, other direction: a value reached by transitions
is the result of evaluation. -/
theorem eval_of_steps {t v : Closed p τ} (hv : Value v) (h : Relation.ReflTransGen Step t v) :
    t ⇓ v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .val hv
  | head hs _ ih => exact eval_of_step hs ih

end Step

/-- Remark 7 and Exercise 22: `t ⇓ v` iff `v` is a value reachable from `t` by
transitions. -/
theorem eval_iff_steps {p : Bool} {τ : Ty} {t v : Closed p τ} :
    t ⇓ v ↔ Value v ∧ Relation.ReflTransGen Step t v :=
  ⟨fun h => ⟨h.value, Step.of_eval h⟩, fun ⟨hv, h⟩ => Step.eval_of_steps hv h⟩

namespace Step

variable {τ : Ty}

private theorem det_aux {p : Bool} (hp : p = false) {t t₁ t₂ : Closed p τ} (h₁ : Step t t₁)
    (h₂ : Step t t₂) : t₁ = t₂ := by
  induction h₁ with
  | succ h ih => cases h₂ with | succ h₂ => rw [ih hp h₂]
  | pred h ih =>
      cases h₂ with
      | pred h₂ => rw [ih hp h₂]
      | predSucc e hv => rw [e] at h; exact (not_of_value hv.succ' h).elim
  | isZero h ih =>
      cases h₂ with
      | isZero h₂ => rw [ih hp h₂]
      | isZeroZero e => rw [e] at h; exact (not_of_value .zero h).elim
      | isZeroSucc e hv => rw [e] at h; exact (not_of_value hv.succ' h).elim
  | predSucc e hv =>
      cases h₂ with
      | pred h₂ => rw [e] at h₂; exact (not_of_value hv.succ' h₂).elim
      | predSucc e₂ => exact Term.succ_injective (e.symm.trans e₂)
  | isZeroZero e =>
      cases h₂ with
      | isZero h₂ => rw [e] at h₂; exact (not_of_value .zero h₂).elim
      | isZeroZero => rfl
      | isZeroSucc e₂ => cases e.symm.trans e₂
  | isZeroSucc e hv =>
      cases h₂ with
      | isZero h₂ => rw [e] at h₂; exact (not_of_value hv.succ' h₂).elim
      | isZeroZero e₂ => cases e.symm.trans e₂
      | isZeroSucc => rfl
  | ite h ih =>
      cases h₂ with
      | ite h₂ => rw [ih hp h₂]
      | iteT e => rw [e] at h; exact (not_of_value .tt h).elim
      | iteF e => rw [e] at h; exact (not_of_value .ff h).elim
  | iteT e =>
      cases h₂ with
      | ite h₂ => rw [e] at h₂; exact (not_of_value .tt h₂).elim
      | iteT => rfl
      | iteF e₂ => cases e.symm.trans e₂
  | iteF e =>
      cases h₂ with
      | ite h₂ => rw [e] at h₂; exact (not_of_value .ff h₂).elim
      | iteT e₂ => cases e.symm.trans e₂
      | iteF => rfl
  | app h ih =>
      cases h₂ with
      | app h₂ => rw [ih hp h₂]
      | beta => exact (not_of_value (.lam _) h).elim
  | beta =>
      cases h₂ with
      | app h₂ => exact (not_of_value (.lam _) h₂).elim
      | beta => rfl
  | fix => cases h₂; rfl
  | porL | porR | porTL | porTR | porFF => cases hp

/-- Transitions of PCF (without `por`) are deterministic. -/
theorem det {t t₁ t₂ : Closed false τ} (h₁ : Step t t₁) (h₂ : Step t t₂) : t₁ = t₂ :=
  det_aux rfl h₁ h₂

/-- PCF transitions (without `por`) are right-unique, i.e. `Step.det` in Mathlib's form. -/
theorem rightUnique : Relator.RightUnique (Step (p := false) (τ := τ)) :=
  fun _ _ _ h₁ h₂ => det h₁ h₂

/-- Transitions of PCF are confluent in CSLib's sense, derived from determinism
through CSLib's `Relation.RightUnique.to_confluent`. -/
theorem confluent : Relation.Confluent (Step (p := false) (τ := τ)) :=
  Relation.RightUnique.to_confluent rightUnique

end Step

end Silmaril.Calculi.PCF
