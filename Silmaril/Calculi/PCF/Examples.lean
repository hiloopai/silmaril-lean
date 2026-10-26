module

public import Silmaril.Calculi.TypedLambda.Raw
public import Silmaril.Calculi.PCF.BigStep
public import Mathlib.Data.Nat.Factorial.Basic

/-! # Programming in PCF

Exercise 13 of the denotational semantics notes (§5.4): addition,
multiplication and factorial, defined with `fix`, compute what they should.
Exercise 12 (Church's `Y` is not typable) holds for every signature and is
`Silmaril.Calculi.TypedLambda.Raw.not_hasType_churchY`.

Arguments are passed by name, so a PCF function may receive an unevaluated
argument. The correctness statements therefore quantify over arbitrary closed
arguments that evaluate to numerals, and specialise to numerals. The
evaluation proofs go through *head expansions* (`Expands`): `t'` expands to
`t` if `t'` evaluates to everything `t` evaluates to.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-! ### Head expansion -/

variable {p : Bool} {σ τ : Ty}

/-- `t'` head-expands to `t`: it evaluates to every value that `t` evaluates to. -/
def Expands (t t' : Closed p τ) : Prop := ∀ ⦃v⦄, t ⇓ v → t' ⇓ v

namespace Expands

theorem refl (t : Closed p τ) : Expands t t := fun _ h => h

theorem trans {t t' t'' : Closed p τ} (h : Expands t t') (h' : Expands t' t'') :
    Expands t t'' := fun _ hv => h' (h hv)

theorem of_eq {t t' : Closed p τ} (h : t = t') : Expands t t' := h ▸ refl t

/-- Head expansion is a congruence for application. -/
theorem app {t t' : Closed p (σ ⤳ τ)} (h : Expands t t') (u : Closed p σ) :
    Expands (.app t u) (.app t' u) := fun v hv => by
  cases hv with
  | val hv => cases hv
  | app ht hs => exact .app (h ht) hs

/-- β-expansion, by rule Fun. -/
theorem beta (t : Term p [σ] τ) (u : Closed p σ) : Expands (t.subst1 u) (.app (.lam t) u) :=
  fun _ h => .app (.val (.lam t)) h

/-- Unfolding a fixed point, by rule Fix. -/
theorem fix (t : Closed p (τ ⤳ τ)) : Expands (.app t (Term.fix t)) (Term.fix t) :=
  fun _ h => .fix' h

/-- Unfolding a recursive function of one argument,
`fix(fun f. fun y. b) u` to `b[fix(fun f. fun y. b)/f, u/y]`. -/
theorem fix_lam₂ {σ' : Ty} (b : Term p [σ, σ ⤳ σ'] σ') (u : Closed p σ) :
    Expands (b.subst (u ::ₜ Subst.single (Term.fix (.lam (.lam b)))))
      (.app (Term.fix (.lam (.lam b))) u) := by
  refine (Expands.trans ?_ ((fix _).app u))
  refine (Expands.trans ?_ ((beta _ _).app u))
  refine Expands.trans (of_eq ?_) (beta _ u)
  rw [TypedLambda.Term.subst_lift_subst1]

end Expands

/-! ### Exercise 13 -/

namespace Term

/-- The variable bound by the second innermost binder. -/
abbrev v1 {Γ : Ctx Base} {σ σ' : Ty} : Term p (σ' :: σ :: Γ) σ := .var (.succ .zero)

/-- The variable bound by the third innermost binder. -/
abbrev v2 {Γ : Ctx Base} {σ σ' σ'' : Ty} : Term p (σ'' :: σ' :: σ :: Γ) σ :=
  .var (.succ (.succ .zero))

end Term

/-- Exercise 13: `plus = fun x:nat. fix(fun (p:nat -> nat) (y:nat).
if zero?(y) then x else succ(p pred(y)))`. -/
def plus : Closed p (Ty.nat ⤳ Ty.nat ⤳ Ty.nat) :=
  .lam (Term.fix (.lam (.lam
    (Term.ite (Term.isZero Term.v0) Term.v2 (Term.succ (.app Term.v1 (Term.pred Term.v0)))))))

/-- Exercise 13: `mul = fun x:nat. fix(fun (t:nat -> nat) (y:nat).
if zero?(y) then 0 else plus x (t pred(y)))`. -/
def mul : Closed p (Ty.nat ⤳ Ty.nat ⤳ Ty.nat) :=
  .lam (Term.fix (.lam (.lam (Term.ite (Term.isZero Term.v0) Term.zero
    (.app (.app (TypedLambda.Term.ofClosed plus) Term.v2) (.app Term.v1 (Term.pred Term.v0)))))))

/-- Exercise 13: a factorial function, `fact = fix(fun (f:nat -> nat) (y:nat).
if zero?(y) then 1 else mul y (f pred(y)))`. -/
def fact : Closed p (Ty.nat ⤳ Ty.nat) :=
  Term.fix (.lam (.lam (Term.ite (Term.isZero Term.v0) (Term.num 1)
    (.app (.app (TypedLambda.Term.ofClosed mul) Term.v0) (.app Term.v1 (Term.pred Term.v0))))))

/-- The recursive part of `plus x` for a closed `x`. -/
def plusRec (a : Closed p .nat) : Closed p ((Ty.nat ⤳ Ty.nat) ⤳ Ty.nat ⤳ Ty.nat) :=
  .lam (.lam (Term.ite (Term.isZero Term.v0) (TypedLambda.Term.ofClosed a)
    (Term.succ (.app Term.v1 (Term.pred Term.v0)))))

theorem plus_expands (a b : Closed p .nat) :
    Expands (.app (Term.fix (plusRec a)) b) (.app (.app plus a) b) :=
  Expands.trans (.of_eq (by simp [plusRec, Subst.lift, Subst.single, Ren.weak]))
    ((Expands.beta _ a).app b)

theorem plusRec_eval {a : Closed p .nat} {m : ℕ} (ha : a ⇓ .num m) (n : ℕ) {b : Closed p .nat}
    (hb : b ⇓ .num n) : .app (Term.fix (plusRec a)) b ⇓ .num (m + n) := by
  induction n generalizing b with
  | zero =>
    refine Expands.fix_lam₂ _ b ?_
    simp
    exact .iteT' (.isZeroZ' hb) ha
  | succ n ih =>
    refine Expands.fix_lam₂ _ b ?_
    simp
    exact .iteF' (.isZeroS' hb) (.succ' (ih (.pred' hb)))

/-- Exercise 13 for arguments that evaluate to numerals: if `a ⇓ m̄` and
`b ⇓ n̄` then `plus a b ⇓ m+n`. -/
theorem plus_eval' {a b : Closed p .nat} {m n : ℕ} (ha : a ⇓ Term.num m) (hb : b ⇓ Term.num n) :
    .app (.app plus a) b ⇓ Term.num (m + n) :=
  plus_expands a b (plusRec_eval ha n hb)

/-- Exercise 13: `plus m̄ n̄ ⇓ m+n`. -/
theorem plus_eval (m n : ℕ) :
    .app (.app plus (Term.num m)) (Term.num n) ⇓ (Term.num (m + n) : Closed p .nat) :=
  plus_eval' (Eval.num m) (Eval.num n)

/-- The recursive part of `mul x` for a closed `x`. -/
def mulRec (a : Closed p .nat) : Closed p ((Ty.nat ⤳ Ty.nat) ⤳ Ty.nat ⤳ Ty.nat) :=
  .lam (.lam (Term.ite (Term.isZero Term.v0) Term.zero
    (.app (.app (TypedLambda.Term.ofClosed plus) (TypedLambda.Term.ofClosed a))
      (.app Term.v1 (Term.pred Term.v0)))))

theorem mul_expands (a b : Closed p .nat) :
    Expands (.app (Term.fix (mulRec a)) b) (.app (.app mul a) b) :=
  Expands.trans (.of_eq (by simp [mulRec, Subst.lift, Subst.single, Ren.weak]))
    ((Expands.beta _ a).app b)

theorem mulRec_eval {a : Closed p .nat} {m : ℕ} (ha : a ⇓ Term.num m) (n : ℕ)
    {b : Closed p .nat} (hb : b ⇓ Term.num n) :
    .app (Term.fix (mulRec a)) b ⇓ Term.num (m * n) := by
  induction n generalizing b with
  | zero =>
    refine Expands.fix_lam₂ _ b ?_
    simp
    exact .iteT' (.isZeroZ' hb) (.val .zero)
  | succ n ih =>
    refine Expands.fix_lam₂ _ b ?_
    simp
    rw [Nat.mul_succ, Nat.add_comm]
    exact .iteF' (.isZeroS' hb) (plus_eval' ha (ih (.pred' hb)))

/-- Exercise 13 for arguments that evaluate to numerals: if `a ⇓ m̄` and
`b ⇓ n̄` then `mul a b ⇓ m⋅n`. -/
theorem mul_eval' {a b : Closed p .nat} {m n : ℕ} (ha : a ⇓ Term.num m) (hb : b ⇓ Term.num n) :
    .app (.app mul a) b ⇓ Term.num (m * n) :=
  mul_expands a b (mulRec_eval ha n hb)

/-- Exercise 13: `mul m̄ n̄ ⇓ m⋅n`. -/
theorem mul_eval (m n : ℕ) :
    .app (.app mul (Term.num m)) (Term.num n) ⇓ (Term.num (m * n) : Closed p .nat) :=
  mul_eval' (Eval.num m) (Eval.num n)

/-- Exercise 13 for an argument that evaluates to a numeral: if `b ⇓ n̄` then
`fact b ⇓ n!`. -/
theorem fact_eval' {b : Closed p .nat} {n : ℕ} (hb : b ⇓ Term.num n) :
    .app fact b ⇓ Term.num n.factorial := by
  induction n generalizing b with
  | zero =>
    refine Expands.fix_lam₂ _ b ?_
    simp
    exact .iteT' (.isZeroZ' hb) (Eval.num 1)
  | succ n ih =>
    refine Expands.fix_lam₂ _ b ?_
    simp
    rw [Nat.factorial_succ]
    exact .iteF' (.isZeroS' hb) (mul_eval' hb (ih (.pred' hb)))

/-- Exercise 13: the factorial function computes the factorial, `fact n̄ ⇓ n!`. -/
theorem fact_eval (n : ℕ) : .app fact (Term.num n) ⇓ (Term.num n.factorial : Closed p .nat) :=
  fact_eval' (Eval.num n)

end Silmaril.Calculi.PCF
