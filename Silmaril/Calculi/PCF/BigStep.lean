module

public import Silmaril.Calculi.PCF.Syntax

/-! # Evaluation

The big-step evaluation relation `t ⇓ v` of Figure 3 of the notes (§5.2), with
the rules PorL, PorR and PorF of Figure 5 for PCF+`por`. The language flag is
an index, so the `por` rules only exist for `p = true`.

Evaluation relates closed terms to values (`Eval.value`) and is deterministic
(Proposition 23), including for PCF+`por` (Exercise 21), even though PorL and
PorR overlap. `Ω` diverges (Example 18), and evaluation does not reduce under
binders (Example 20). The rules can be inverted for a known operator
(`Eval.app_lam_iff`, `Eval.pred_iff`, `Eval.ite_iff`, ...).
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Figure 3 and Figure 5: the closed term `t` evaluates to the value `v`.

As for `Value`, rules about operators quantify over the argument tuple; the
`Eval.succ'`-style lemmas below restate them with the smart constructors. -/
inductive Eval : {p : Bool} → {τ : Ty} → Closed p τ → Closed p τ → Prop
  /-- Val. -/
  | val {p : Bool} {τ : Ty} {v : Closed p τ} : Value v → Eval v v
  /-- Succ. -/
  | succ {p : Bool} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      Eval args.head v → Eval (.op .succ args) (.succ v)
  /-- Pred. -/
  | pred {p : Bool} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      Eval args.head (.succ v) → Eval (.op .pred args) v
  /-- ZeroZ. -/
  | isZeroZ {p : Bool} {args : Tuple (Closed p) [.nat]} :
      Eval args.head .zero → Eval (.op .isZero args) .tt
  /-- ZeroS. -/
  | isZeroS {p : Bool} {args : Tuple (Closed p) [.nat]} {v : Closed p .nat} :
      Eval args.head (.succ v) → Eval (.op .isZero args) .ff
  /-- IfT. -/
  | iteT {p : Bool} {τ : Ty} {args : Tuple (Closed p) [.bool, τ, τ]} {v : Closed p τ} :
      Eval args.head .tt → Eval args.tail.head v → Eval (.op (.ite τ) args) v
  /-- IfF. -/
  | iteF {p : Bool} {τ : Ty} {args : Tuple (Closed p) [.bool, τ, τ]} {v : Closed p τ} :
      Eval args.head .ff → Eval args.tail.tail.head v → Eval (.op (.ite τ) args) v
  /-- Fun (call-by-name application). -/
  | app {p : Bool} {σ τ : Ty} {t : Closed p (σ ⤳ τ)} {t' : Term p [σ] τ} {u : Closed p σ}
      {v : Closed p τ} :
      Eval t (.lam t') → Eval (t'.subst1 u) v → Eval (.app t u) v
  /-- Fix. -/
  | fix {p : Bool} {τ : Ty} {args : Tuple (Closed p) [τ ⤳ τ]} {v : Closed p τ} :
      Eval (.app args.head (.op (.fix τ) args)) v → Eval (.op (.fix τ) args) v
  /-- PorL. -/
  | porL {args : Tuple (Closed true) [.bool, .bool]} :
      Eval args.head .tt → Eval (.op .por args) .tt
  /-- PorR. -/
  | porR {args : Tuple (Closed true) [.bool, .bool]} :
      Eval args.tail.head .tt → Eval (.op .por args) .tt
  /-- PorF. -/
  | porF {args : Tuple (Closed true) [.bool, .bool]} :
      Eval args.head .ff → Eval args.tail.head .ff → Eval (.op .por args) .ff

@[inherit_doc] infix:50 " ⇓ " => Eval

/-- `t` has no result (`t ⇑`). This is Isotope's `NoResult`, not an infinite reduction:
stuck terms such as `pred 𝟶` diverge in this sense. See `PCF.Divergence`. -/
def Diverges {p : Bool} {τ : Ty} (t : Closed p τ) : Prop := ∀ v, ¬ t ⇓ v

namespace Eval

variable {p : Bool} {τ : Ty}

/-- Succ, with the smart constructors. -/
theorem succ' {t v : Closed p .nat} (h : t ⇓ v) : .succ t ⇓ .succ v := .succ h

/-- Pred, with the smart constructors. -/
theorem pred' {t v : Closed p .nat} (h : t ⇓ .succ v) : .pred t ⇓ v := .pred h

/-- ZeroZ, with the smart constructors. -/
theorem isZeroZ' {t : Closed p .nat} (h : t ⇓ .zero) : .isZero t ⇓ .tt := .isZeroZ h

/-- ZeroS, with the smart constructors. -/
theorem isZeroS' {t v : Closed p .nat} (h : t ⇓ .succ v) : .isZero t ⇓ .ff := .isZeroS h

/-- IfT, with the smart constructors. -/
theorem iteT' {b : Closed p .bool} {t t' v : Closed p τ} (hb : b ⇓ .tt) (ht : t ⇓ v) :
    .ite b t t' ⇓ v := .iteT hb ht

/-- IfF, with the smart constructors. -/
theorem iteF' {b : Closed p .bool} {t t' v : Closed p τ} (hb : b ⇓ .ff) (ht : t' ⇓ v) :
    .ite b t t' ⇓ v := .iteF hb ht

/-- Fix, with the smart constructors. -/
theorem fix' {t : Closed p (τ ⤳ τ)} {v : Closed p τ} (h : .app t (Term.fix t) ⇓ v) :
    Term.fix t ⇓ v := .fix h

/-- Evaluation produces values. -/
theorem value {t v : Closed p τ} (h : t ⇓ v) : Value v := by
  induction h with
  | val hv => exact hv
  | succ _ ih => exact .succ' ih
  | pred _ ih => cases ih with | succ hv => exact hv
  | isZeroZ | porL | porR => exact .tt
  | isZeroS | porF => exact .ff
  | iteT _ _ _ ih | iteF _ _ _ ih | app _ _ _ ih | fix _ ih => exact ih

/-- A value evaluates only to itself. -/
theorem of_value {v w : Closed p τ} (hv : Value v) (h : v ⇓ w) : w = v := by
  induction hv with
  | @succ args _ ih =>
      cases h with
      | val => rfl
      | succ h => rw [ih h, Term.succ_head]
  | _ => cases h; rfl

theorem value_iff {v w : Closed p τ} (hv : Value v) : v ⇓ w ↔ w = v :=
  ⟨of_value hv, fun h => by subst h; exact .val hv⟩

theorem num (n : ℕ) : (Term.num n : Closed p .nat) ⇓ Term.num n := .val (Value.num n)

/-- Proposition 23 and Exercise 21: evaluation is deterministic. -/
theorem det {t v w : Closed p τ} (h₁ : t ⇓ v) (h₂ : t ⇓ w) : v = w := by
  induction h₁ with
  | val hv => exact (of_value hv h₂).symm
  | @succ _ args _ h ih =>
      cases h₂ with
      | val hv =>
          cases hv with | succ hv => rw [of_value hv h, Term.succ_head]
      | succ h₂ => rw [ih h₂]
  | pred h ih =>
      cases h₂ with
      | val hv => cases hv
      | pred h₂ => exact Term.succ_injective (ih h₂)
  | isZeroZ h ih =>
      cases h₂ with
      | val hv => cases hv
      | isZeroZ => rfl
      | isZeroS h₂ => cases ih h₂
  | isZeroS h ih =>
      cases h₂ with
      | val hv => cases hv
      | isZeroZ h₂ => cases ih h₂
      | isZeroS => rfl
  | iteT hb ht ihb iht =>
      cases h₂ with
      | val hv => cases hv
      | iteT _ h₂ => exact iht h₂
      | iteF hb₂ _ => cases ihb hb₂
  | iteF hb ht ihb iht =>
      cases h₂ with
      | val hv => cases hv
      | iteT hb₂ _ => cases ihb hb₂
      | iteF _ h₂ => exact iht h₂
  | app ht hs iht ihs =>
      cases h₂ with
      | val hv => cases hv
      | app ht₂ hs₂ =>
          cases iht ht₂
          exact ihs hs₂
  | fix h ih =>
      cases h₂ with
      | val hv => cases hv
      | fix h₂ => exact ih h₂
  | porL h ih =>
      cases h₂ with
      | val hv => cases hv
      | porL | porR => rfl
      | porF h₂ => cases ih h₂
  | porR h ih =>
      cases h₂ with
      | val hv => cases hv
      | porL | porR => rfl
      | porF _ h₂ => cases ih h₂
  | porF h h' ih ih' =>
      cases h₂ with
      | val hv => cases hv
      | porL h₂ => cases ih h₂
      | porR h₂ => cases ih' h₂
      | porF => rfl

/-! ### Inversion of evaluation -/

/-- `(fun x. t) u ⇓ v` iff `t[u/x] ⇓ v`. -/
theorem app_lam_iff {σ τ : Ty} {t : Term p [σ] τ} {u : Closed p σ} {v : Closed p τ} :
    .app (.lam t) u ⇓ v ↔ t.subst1 u ⇓ v := by
  refine ⟨fun h => ?_, fun h => .app (.val (.lam _)) h⟩
  cases h with
  | val hv => cases hv
  | app ht hs =>
      cases Eval.of_value (.lam _) ht
      exact hs

/-- `pred(t) ⇓ v` iff `t ⇓ succ(v)`. -/
theorem pred_iff {t v : Closed p .nat} : .pred t ⇓ v ↔ t ⇓ .succ v := by
  refine ⟨fun h => ?_, pred'⟩
  cases h with
  | val hv => cases hv
  | pred h => exact h

/-- `zero?(t) ⇓ true` iff `t ⇓ 𝟶`. -/
theorem isZero_tt_iff {t : Closed p .nat} : .isZero t ⇓ .tt ↔ t ⇓ .zero := by
  refine ⟨fun h => ?_, isZeroZ'⟩
  cases h with
  | isZeroZ h => exact h

/-- `zero?(t) ⇓ false` iff `t` evaluates to a successor. -/
theorem isZero_ff_iff {t : Closed p .nat} : .isZero t ⇓ .ff ↔ ∃ v, t ⇓ .succ v := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => isZeroS' h⟩
  cases h with
  | isZeroS h => exact ⟨_, h⟩

/-- `if b then t else t' ⇓ v` iff `b` selects a branch that evaluates to `v`. -/
theorem ite_iff {τ : Ty} {b : Closed p .bool} {t t' v : Closed p τ} :
    .ite b t t' ⇓ v ↔ (b ⇓ .tt ∧ t ⇓ v) ∨ (b ⇓ .ff ∧ t' ⇓ v) := by
  refine ⟨fun h => ?_, fun h => h.elim (fun h => iteT' h.1 h.2) fun h => iteF' h.1 h.2⟩
  cases h with
  | val hv => cases hv
  | iteT hb ht => exact .inl ⟨hb, ht⟩
  | iteF hb ht => exact .inr ⟨hb, ht⟩

/-- `true ⇓ false` fails. -/
theorem not_tt_ff : ¬ (Term.tt : Closed p .bool) ⇓ .ff := fun h => by
  cases of_value .tt h

/-- `false ⇓ true` fails. -/
theorem not_ff_tt : ¬ (Term.ff : Closed p .bool) ⇓ .tt := fun h => by
  cases of_value .ff h

end Eval

section Omega

variable {p : Bool}

/-- The invariant behind Example 18: no derivation concludes with `Ω` or with
its one-step unfolding `(fun x. x) Ω`. -/
private theorem not_eval_omega_aux {τ : Ty} {t v : Closed p τ} (h : t ⇓ v) :
    t ≠ Term.omega τ ∧ t ≠ .app (.lam Term.v0) (Term.omega τ) := by
  induction h with
  | val hv => exact ⟨fun e => (by subst e; cases hv), fun e => (by subst e; cases hv)⟩
  | app ht hs _ ihs =>
      refine ⟨fun e => (by cases e), fun e => ?_⟩
      cases e
      cases Eval.of_value (.lam _) ht
      exact ihs.1 rfl
  | @fix _ τ args _ _ ih =>
      refine ⟨fun e => ?_, fun e => (by cases e)⟩
      have hargs : args = Tuple.single (.lam Term.v0) := by
        injection e with _ _ _ _ e
      subst hargs
      exact ih.2 rfl
  | _ => exact ⟨fun e => (by cases e), fun e => (by cases e)⟩

/-- Example 18: `Ωτ = fix(fun x:τ. x)` diverges. -/
theorem omega_diverges {τ : Ty} : Diverges (Term.omega (p := p) (Γ := []) τ) :=
  fun _ h => (not_eval_omega_aux h).1 rfl

end Omega

section Example20

variable {p : Bool}

/-- The value `fun x:nat. (fun y:nat. y) 𝟶` of Example 20: a β-redex under a
binder. -/
abbrev lamBetaZero (p : Bool) : Closed p (Ty.nat ⤳ Ty.nat) :=
  .lam (.app (.lam Term.v0) Term.zero)

/-- The value `fun x:nat. 𝟶` of Example 20, the contractum of `lamBetaZero`. -/
abbrev lamZero (p : Bool) : Closed p (Ty.nat ⤳ Ty.nat) := .lam Term.zero

/-- Example 20: evaluation does not reduce under binders, so `lamBetaZero`
does not evaluate to `lamZero`. -/
theorem not_eval_lamBetaZero : ¬ lamBetaZero p ⇓ lamZero p :=
  fun h => by cases Eval.of_value (.lam _) h

end Example20

end Silmaril.Calculi.PCF
