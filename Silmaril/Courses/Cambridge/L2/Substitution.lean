module

public import Silmaril.Courses.Cambridge.L2.Syntax
public import Silmaril.Prelude.DeBruijn

/-! # Cambridge L2 substitution, §4.1

Bound occurrences are de Bruijn indices. `rename` changes ambient indices;
`subst` replaces them simultaneously. Both operations lift through each binder,
including the two binders in a recursive function body. `substFree` replaces a
free *name* and shifts the replacement when crossing a binder, so it cannot be
captured. These operations implement the substitutions on pp. 53–55.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

/-- Rename ambient bound indices, preserving indices introduced by a binder. -/
def Expr.rename (ρ : Nat → Nat) : Expr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (left.rename ρ) op (right.rename ρ)
  | .cond test yes no => .cond (test.rename ρ) (yes.rename ρ) (no.rename ρ)
  | .assign loc value => .assign loc (value.rename ρ)
  | .deref loc => .deref loc
  | .skip => .skip
  | .seq left right => .seq (left.rename ρ) (right.rename ρ)
  | .loop test body => .loop (test.rename ρ) (body.rename ρ)
  | .bvar index => .bvar (ρ index)
  | .fvar name => .fvar name
  | .lam domain body => .lam domain (body.rename (DeBruijn.lift ρ))
  | .app function argument => .app (function.rename ρ) (argument.rename ρ)
  | .letE type value body =>
      .letE type (value.rename ρ) (body.rename (DeBruijn.lift ρ))
  | .letRecFun domain codomain functionBody body =>
      .letRecFun domain codomain
        (functionBody.rename (DeBruijn.liftN 2 ρ))
        (body.rename (DeBruijn.lift ρ))

theorem Expr.rename_id (e : Expr) : e.rename id = e := by
  induction e with
  | int | bool | deref | skip | bvar | fvar => rfl
  | binary left op right ihLeft ihRight => simp [rename, ihLeft, ihRight]
  | cond test yes no ihTest ihYes ihNo => simp [rename, ihTest, ihYes, ihNo]
  | assign loc value ih => simp [rename, ih]
  | seq left right ihLeft ihRight => simp [rename, ihLeft, ihRight]
  | loop test body ihTest ihBody => simp [rename, ihTest, ihBody]
  | lam domain body ih => simpa [rename] using ih
  | app function argument ihFunction ihArgument =>
      simp [rename, ihFunction, ihArgument]
  | letE type value body ihValue ihBody =>
      simpa [rename] using And.intro ihValue ihBody
  | letRecFun domain codomain functionBody body ihFunction ihBody =>
      simp [rename, ihFunction, ihBody]

theorem Expr.rename_comp (e : Expr) (ρ σ : Nat → Nat) :
    (e.rename ρ).rename σ = e.rename (σ ∘ ρ) := by
  induction e generalizing ρ σ with
  | int | bool | deref | skip | fvar => rfl
  | bvar => rfl
  | binary left op right ihLeft ihRight =>
      simp [rename, ihLeft, ihRight]
  | cond test yes no ihTest ihYes ihNo =>
      simp [rename, ihTest, ihYes, ihNo]
  | assign loc value ih => simp [rename, ih]
  | seq left right ihLeft ihRight => simp [rename, ihLeft, ihRight]
  | loop test body ihTest ihBody => simp [rename, ihTest, ihBody]
  | lam domain body ih =>
      simpa only [rename, DeBruijn.lift_comp] using
        congrArg (Expr.lam domain) (ih (DeBruijn.lift ρ) (DeBruijn.lift σ))
  | app function argument ihFunction ihArgument =>
      simp [rename, ihFunction, ihArgument]
  | letE type value body ihValue ihBody =>
      simp only [rename, ihValue, ihBody, DeBruijn.lift_comp]
  | letRecFun domain codomain functionBody body ihFunction ihBody =>
      simp only [rename, ihFunction, ihBody,
        DeBruijn.lift_comp, DeBruijn.liftN_comp]

theorem Expr.freeVars_rename (e : Expr) (ρ : Nat → Nat) :
    (e.rename ρ).freeVars = e.freeVars := by
  induction e generalizing ρ with
  | int | bool | deref | skip | bvar | fvar => rfl
  | binary left op right ihLeft ihRight =>
      simp [rename, freeVars, ihLeft, ihRight]
  | cond test yes no ihTest ihYes ihNo =>
      simp [rename, freeVars, ihTest, ihYes, ihNo]
  | assign loc value ih => simp [rename, freeVars, ih]
  | seq left right ihLeft ihRight => simp [rename, freeVars, ihLeft, ihRight]
  | loop test body ihTest ihBody => simp [rename, freeVars, ihTest, ihBody]
  | lam domain body ih => simp [rename, freeVars, ih]
  | app function argument ihFunction ihArgument =>
      simp [rename, freeVars, ihFunction, ihArgument]
  | letE type value body ihValue ihBody =>
      simp [rename, freeVars, ihValue, ihBody]
  | letRecFun domain codomain functionBody body ihFunction ihBody =>
      simp [rename, freeVars, ihFunction, ihBody]

/-- Enter one binder in a simultaneous substitution. -/
def Expr.liftSubst (σ : Nat → Expr) : Nat → Expr
  | 0 => .bvar 0
  | index + 1 => (σ index).rename Nat.succ

/-- Simultaneously replace ambient bound indices. -/
def Expr.subst (σ : Nat → Expr) : Expr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (left.subst σ) op (right.subst σ)
  | .cond test yes no => .cond (test.subst σ) (yes.subst σ) (no.subst σ)
  | .assign loc value => .assign loc (value.subst σ)
  | .deref loc => .deref loc
  | .skip => .skip
  | .seq left right => .seq (left.subst σ) (right.subst σ)
  | .loop test body => .loop (test.subst σ) (body.subst σ)
  | .bvar index => σ index
  | .fvar name => .fvar name
  | .lam domain body => .lam domain (body.subst (liftSubst σ))
  | .app function argument => .app (function.subst σ) (argument.subst σ)
  | .letE type value body =>
      .letE type (value.subst σ) (body.subst (liftSubst σ))
  | .letRecFun domain codomain functionBody body =>
      .letRecFun domain codomain
        (functionBody.subst (liftSubst (liftSubst σ)))
        (body.subst (liftSubst σ))

theorem Expr.liftSubst_bvar : Expr.liftSubst Expr.bvar = Expr.bvar := by
  funext index
  cases index <;> rfl

theorem Expr.subst_id (e : Expr) : e.subst Expr.bvar = e := by
  induction e with
  | int | bool | deref | skip | bvar | fvar => rfl
  | binary left op right ihLeft ihRight => simp [subst, ihLeft, ihRight]
  | cond test yes no ihTest ihYes ihNo =>
      simp [subst, ihTest, ihYes, ihNo]
  | assign loc value ih => simp [subst, ih]
  | seq left right ihLeft ihRight => simp [subst, ihLeft, ihRight]
  | loop test body ihTest ihBody => simp [subst, ihTest, ihBody]
  | lam domain body ih => simpa [subst, liftSubst_bvar] using ih
  | app function argument ihFunction ihArgument =>
      simp [subst, ihFunction, ihArgument]
  | letE type value body ihValue ihBody =>
      simp [subst, liftSubst_bvar, ihValue, ihBody]
  | letRecFun domain codomain functionBody body ihFunction ihBody =>
      simp [subst, liftSubst_bvar, ihFunction, ihBody]

/-- Remove the innermost binder and replace its occurrences with `argument`. -/
def Expr.beta (body argument : Expr) : Expr :=
  body.subst (fun
    | 0 => argument
    | index + 1 => .bvar index)

/-- Replace a free name without capturing any ambient bound indices in the replacement. -/
def Expr.substFree (expression : Expr) (name : Var) (replacement : Expr) : Expr :=
  match expression with
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right =>
      .binary (left.substFree name replacement) op (right.substFree name replacement)
  | .cond test yes no =>
      .cond (test.substFree name replacement)
        (yes.substFree name replacement) (no.substFree name replacement)
  | .assign loc value => .assign loc (value.substFree name replacement)
  | .deref loc => .deref loc
  | .skip => .skip
  | .seq left right =>
      .seq (left.substFree name replacement) (right.substFree name replacement)
  | .loop test body =>
      .loop (test.substFree name replacement) (body.substFree name replacement)
  | .bvar index => .bvar index
  | .fvar other => if other = name then replacement else .fvar other
  | .lam domain body =>
      .lam domain (body.substFree name (replacement.rename Nat.succ))
  | .app function argument =>
      .app (function.substFree name replacement)
        (argument.substFree name replacement)
  | .letE type value body =>
      .letE type (value.substFree name replacement)
        (body.substFree name (replacement.rename Nat.succ))
  | .letRecFun domain codomain functionBody body =>
      .letRecFun domain codomain
        (functionBody.substFree name (replacement.rename (fun index => index + 2)))
        (body.substFree name (replacement.rename Nat.succ))

end Silmaril.Courses.Cambridge.L2
