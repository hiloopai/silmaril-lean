module

public import Silmaril.Courses.Cambridge.L2.Typing

/-! # Cambridge L2 substitution lemma, Exercise 24

This is Lemma 20 on p. 59 in the locally nameless representation. It proves
the stronger simultaneous-substitution statement, then specializes it to
replacing the nearest bound variable at a beta or `let` redex. The proof also
handles the two binders in a recursive function body.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

def BoundCompatible (Γ Δ : TypeEnv) (ρ : Nat → Nat) : Prop :=
  ∀ index T, Γ.bound[index]? = some T → Δ.bound[ρ index]? = some T

theorem BoundCompatible.push {Γ Δ : TypeEnv} {ρ : Nat → Nat}
    (compatible : BoundCompatible Γ Δ ρ) (A : Ty) :
    BoundCompatible (Γ.push A) (Δ.push A) (DeBruijn.lift ρ) := by
  intro index T lookup
  cases index with
  | zero => simpa only [TypeEnv.push, List.getElem?_cons_zero, DeBruijn.lift] using lookup
  | succ index =>
      apply compatible index T
      simpa only [TypeEnv.push, List.getElem?_cons_succ] using lookup

theorem BoundCompatible.pushTwo {Γ Δ : TypeEnv} {ρ : Nat → Nat}
    (compatible : BoundCompatible Γ Δ ρ) (A B : Ty) :
    BoundCompatible ((Γ.push A).push B) ((Δ.push A).push B)
      (DeBruijn.liftN 2 ρ) := by
  exact (compatible.push A).push B

theorem HasType.rename {Γ Δ : TypeEnv} {e : Expr} {T : Ty}
    (typing : HasType Γ e T) (ρ : Nat → Nat)
    (locs : Γ.locs = Δ.locs) (free : Γ.free = Δ.free)
    (compatible : BoundCompatible Γ Δ ρ) :
    HasType Δ (e.rename ρ) T := by
  induction typing generalizing Δ ρ with
  | int n => exact .int n
  | bool b => exact .bool b
  | add hl hr ihl ihr => exact .add (ihl ρ locs free compatible) (ihr ρ locs free compatible)
  | ge hl hr ihl ihr => exact .ge (ihl ρ locs free compatible) (ihr ρ locs free compatible)
  | cond hc hy hn ihc ihy ihn =>
      exact .cond (ihc ρ locs free compatible)
        (ihy ρ locs free compatible) (ihn ρ locs free compatible)
  | assign present he ih =>
      exact .assign (by simpa [← locs] using present) (ih ρ locs free compatible)
  | deref present => exact .deref (by simpa [← locs] using present)
  | skip => exact .skip
  | seq hl hr ihl ihr => exact .seq (ihl ρ locs free compatible) (ihr ρ locs free compatible)
  | loop ht hb iht ihb => exact .loop (iht ρ locs free compatible) (ihb ρ locs free compatible)
  | bvar lookup => exact .bvar (compatible _ _ lookup)
  | fvar lookup => exact .fvar (by simpa [← free] using lookup)
  | lam typing ih =>
      exact .lam (ih (DeBruijn.lift ρ) locs free (compatible.push _))
  | app hf ha ihf iha => exact .app (ihf ρ locs free compatible) (iha ρ locs free compatible)
  | letE hv hb ihv ihb =>
      exact .letE (ihv ρ locs free compatible)
        (ihb (DeBruijn.lift ρ) locs free (compatible.push _))
  | letRecFun hf hb ihf ihb =>
      exact .letRecFun
        (ihf (DeBruijn.liftN 2 ρ) locs free (compatible.pushTwo _ _))
        (ihb (DeBruijn.lift ρ) locs free (compatible.push _))

def TypedSubst (Γ Δ : TypeEnv) (σ : Nat → Expr) : Prop :=
  ∀ index T, Γ.bound[index]? = some T → HasType Δ (σ index) T

theorem TypedSubst.push {Γ Δ : TypeEnv} {σ : Nat → Expr}
    (compatible : TypedSubst Γ Δ σ) (A : Ty) :
    TypedSubst (Γ.push A) (Δ.push A) (Expr.liftSubst σ) := by
  intro index T lookup
  cases index with
  | zero => exact .bvar (by simpa [TypeEnv.push] using lookup)
  | succ index =>
      apply (compatible index T (by simpa [TypeEnv.push] using lookup)).rename
        (Δ := Δ.push A) Nat.succ rfl rfl
      intro i B present
      simpa [TypeEnv.push] using present

theorem TypedSubst.pushTwo {Γ Δ : TypeEnv} {σ : Nat → Expr}
    (compatible : TypedSubst Γ Δ σ) (A B : Ty) :
    TypedSubst ((Γ.push A).push B) ((Δ.push A).push B)
      (Expr.liftSubst (Expr.liftSubst σ)) :=
  (compatible.push A).push B

/-- Simultaneous substitution preserves typing when every replacement has the
type of its corresponding bound variable. -/
theorem HasType.subst {Γ Δ : TypeEnv} {e : Expr} {T : Ty}
    (typing : HasType Γ e T) (σ : Nat → Expr)
    (locs : Γ.locs = Δ.locs) (free : Γ.free = Δ.free)
    (compatible : TypedSubst Γ Δ σ) :
    HasType Δ (e.subst σ) T := by
  induction typing generalizing Δ σ with
  | int n => exact .int n
  | bool b => exact .bool b
  | add hl hr ihl ihr => exact .add (ihl σ locs free compatible) (ihr σ locs free compatible)
  | ge hl hr ihl ihr => exact .ge (ihl σ locs free compatible) (ihr σ locs free compatible)
  | cond hc hy hn ihc ihy ihn =>
      exact .cond (ihc σ locs free compatible)
        (ihy σ locs free compatible) (ihn σ locs free compatible)
  | assign present he ih =>
      exact .assign (by simpa [← locs] using present) (ih σ locs free compatible)
  | deref present => exact .deref (by simpa [← locs] using present)
  | skip => exact .skip
  | seq hl hr ihl ihr => exact .seq (ihl σ locs free compatible) (ihr σ locs free compatible)
  | loop ht hb iht ihb => exact .loop (iht σ locs free compatible) (ihb σ locs free compatible)
  | bvar lookup => exact compatible _ _ lookup
  | fvar lookup => exact .fvar (by simpa [← free] using lookup)
  | lam typing ih =>
      exact .lam (ih (Expr.liftSubst σ) locs free (compatible.push _))
  | app hf ha ihf iha => exact .app (ihf σ locs free compatible) (iha σ locs free compatible)
  | letE hv hb ihv ihb =>
      exact .letE (ihv σ locs free compatible)
        (ihb (Expr.liftSubst σ) locs free (compatible.push _))
  | letRecFun hf hb ihf ihb =>
      exact .letRecFun
        (ihf (Expr.liftSubst (Expr.liftSubst σ)) locs free
          (compatible.pushTwo _ _))
        (ihb (Expr.liftSubst σ) locs free (compatible.push _))

/-- Lemma 20 for one binder: the beta/let replacement keeps the body's type. -/
theorem HasType.beta {Γ : TypeEnv} {body argument : Expr} {A B : Ty}
    (bodyType : HasType (Γ.push A) body B)
    (argumentType : HasType Γ argument A) :
    HasType Γ (body.beta argument) B := by
  apply bodyType.subst (Δ := Γ) (fun
    | 0 => argument
    | index + 1 => .bvar index) rfl rfl
  intro index T lookup
  cases index with
  | zero =>
      have same : A = T := Option.some.inj (by simpa [TypeEnv.push] using lookup)
      cases same
      exact argumentType
  | succ index =>
      exact .bvar (by simpa [TypeEnv.push] using lookup)

end Silmaril.Courses.Cambridge.L2
