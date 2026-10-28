module

public import Silmaril.Calculi.PCF.BigStep

/-! # Call-by-value evaluation

Remark 6 of the notes: replacing rule Fun by Fun-CBV, which evaluates the
argument before substituting it, gives a call-by-value semantics. The
difference is visible on `(fun x:nat. 𝟶) Ω`, which evaluates to `𝟶` under
call-by-name but diverges under call-by-value.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Figure 3 with rule Fun replaced by Fun-CBV. -/
inductive EvalV : {p : Bool} → {τ : Ty} → Closed p τ → Closed p τ → Prop
  | val {p : Bool} {τ : Ty} {v : Closed p τ} : Value v → EvalV v v
  | succ {p : Bool} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      EvalV args.head v → EvalV (.op .succ args) (.succ v)
  | pred {p : Bool} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      EvalV args.head (.succ v) → EvalV (.op .pred args) v
  | isZeroZ {p : Bool} {args : Tuple (Closed p) [.nat]} :
      EvalV args.head .zero → EvalV (.op .isZero args) .tt
  | isZeroS {p : Bool} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      EvalV args.head (.succ v) → EvalV (.op .isZero args) .ff
  | iteT {p : Bool} {τ : Ty} {args : Tuple (Closed p) [.bool, τ, τ]} {v : Closed p τ} :
      EvalV args.head .tt → EvalV args.tail.head v → EvalV (.op (.ite τ) args) v
  | iteF {p : Bool} {τ : Ty} {args : Tuple (Closed p) [.bool, τ, τ]} {v : Closed p τ} :
      EvalV args.head .ff → EvalV args.tail.tail.head v → EvalV (.op (.ite τ) args) v
  /-- Fun-CBV. -/
  | app {p : Bool} {σ τ : Ty} {t : Closed p (σ ⤳ τ)} {t' : Term p [σ] τ} {u v' : Closed p σ}
      {v : Closed p τ} :
      EvalV t (.lam t') → EvalV u v' → EvalV (t'.subst1 v') v → EvalV (.app t u) v
  | fix {p : Bool} {τ : Ty} {args : Tuple (Closed p) [τ ⤳ τ]} {v : Closed p τ} :
      EvalV (.app args.head (.op (.fix τ) args)) v → EvalV (.op (.fix τ) args) v
  | porL {args : Tuple (Closed true) [.bool, .bool]} :
      EvalV args.head .tt → EvalV (.op .por args) .tt
  | porR {args : Tuple (Closed true) [.bool, .bool]} :
      EvalV args.tail.head .tt → EvalV (.op .por args) .tt
  | porF {args : Tuple (Closed true) [.bool, .bool]} :
      EvalV args.head .ff → EvalV args.tail.head .ff → EvalV (.op .por args) .ff

namespace EvalV

variable {p : Bool}

theorem of_value {τ : Ty} {v w : Closed p τ} (hv : Value v) (h : EvalV v w) : w = v := by
  induction hv with
  | @succ args _ ih =>
      cases h with
      | val => rfl
      | succ h => rw [ih h, Term.succ_head]
  | _ => cases h; rfl

private theorem not_omega_aux {τ : Ty} {t v : Closed p τ} (h : EvalV t v) :
    t ≠ Term.omega τ ∧ t ≠ .app (.lam Term.v0) (Term.omega τ) := by
  induction h with
  | val hv => exact ⟨fun e => (by subst e; cases hv), fun e => (by subst e; cases hv)⟩
  | app _ _ _ _ ihu _ =>
      refine ⟨fun e => (by cases e), fun e => ?_⟩
      cases e
      exact ihu.1 rfl
  | fix _ ih =>
      refine ⟨fun e => ?_, fun e => (by cases e)⟩
      cases e
      exact ih.2 rfl
  | _ => exact ⟨fun e => (by cases e), fun e => (by cases e)⟩

/-- `Ω` diverges under call-by-value too. -/
theorem omega_diverges {τ : Ty} (v : Closed p τ) : ¬ EvalV (Term.omega τ) v :=
  fun h => (not_omega_aux h).1 rfl

end EvalV

/-- The program `(fun x:nat. 𝟶) Ω` of Remark 6. -/
abbrev constZeroOmega (p : Bool) : Closed p .nat := .app (.lam Term.zero) (Term.omega .nat)

/-- Remark 6: under call-by-name, `(fun x:nat. 𝟶) Ω` evaluates to `𝟶`. -/
theorem constZeroOmega_eval (p : Bool) : constZeroOmega p ⇓ .zero :=
  .app (.val (.lam _)) (by rw [TypedLambda.Term.subst1, TypedLambda.Term.subst_op_nil]; exact .val .zero)

/-- Remark 6: under call-by-value, `(fun x:nat. 𝟶) Ω` diverges. -/
theorem constZeroOmega_evalV (p : Bool) (v : Closed p .nat) : ¬ EvalV (constZeroOmega p) v := by
  intro h
  cases h with
  | val hv => cases hv
  | app _ hu _ => exact EvalV.omega_diverges _ hu

end Silmaril.Calculi.PCF
