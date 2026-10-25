module

public import Silmaril.Logic.HOLLight.Type

@[expose] public section

/-!
# Raw locally nameless HOL Light terms

Bound variables are de Bruijn indices. A free variable is a name together with
its type: type instantiation may identify formerly distinct free variables.
Primitive equality and choice carry their type instances explicitly, as do
user constants. There are no term-level Boolean or individual literals.
-/

namespace Silmaril.Logic.HOLLight

/-- Constants with explicit polymorphic instances. -/
inductive Const where
  | eq (type : Ty)
  | select (type : Ty)
  | user (name : Nat) (types : List Ty)
  deriving DecidableEq, Repr

namespace Const

/-- Instantiate all type annotations of a constant. -/
def tySubst (σ : Nat → Ty) : Const → Const
  | .eq A => .eq (A.subst σ)
  | .select A => .select (A.subst σ)
  | .user c As => .user c (As.map (Ty.subst σ))

@[simp] theorem tySubst_id (c : Const) : c.tySubst Ty.var = c := by
  have h : Ty.subst Ty.var = id := funext Ty.subst_id
  cases c <;> simp [tySubst, h]

theorem tySubst_comp (σ τ : Nat → Ty) (c : Const) :
    (c.tySubst σ).tySubst τ = c.tySubst (fun i => (σ i).subst τ) := by
  cases c <;> simp [tySubst, List.map_map, Function.comp_def, Ty.subst_comp]

end Const

/-- Raw syntax; scoping and typing are separate judgments. -/
inductive Tm where
  | bvar (index : Nat)
  | fvar (name : Nat) (type : Ty)
  | const (constant : Const)
  | app (function argument : Tm)
  | lam (domain : Ty) (body : Tm)
  deriving DecidableEq, Repr

namespace Tm

/-- Object-level equality, formed from the polymorphic equality constant. -/
def equal (A : Ty) (left right : Tm) : Tm := .app (.app (.const (.eq A)) left) right

/-- Fully applied Hilbert choice. -/
def select (A : Ty) (predicate : Tm) : Tm := .app (.const (.select A)) predicate

/-- Every bound index refers to one of the ambient or enclosing binders. -/
def Scope (depth : Nat) : Tm → Prop
  | .bvar i => i < depth
  | .fvar _ _ | .const _ => True
  | .app f x => Scope depth f ∧ Scope depth x
  | .lam _ b => Scope (depth + 1) b

/-- Locally closed terms may still have named free variables. -/
abbrev Closed (t : Tm) : Prop := Scope 0 t

/-- Finite free support, retaining types in variable identities. -/
def freeVars : Tm → List (Nat × Ty)
  | .bvar _ | .const _ => []
  | .fvar n A => [(n, A)]
  | .app f x => f.freeVars ++ x.freeVars
  | .lam _ b => b.freeVars

/-- Freshness uses the full typed name. -/
def Fresh (v : Nat × Ty) (t : Tm) : Prop := v ∉ t.freeVars

/-- Simultaneous type instantiation, including types of named free variables. -/
def tySubst (σ : Nat → Ty) : Tm → Tm
  | .bvar i => .bvar i
  | .fvar n A => .fvar n (A.subst σ)
  | .const c => .const (c.tySubst σ)
  | .app f x => .app (f.tySubst σ) (x.tySubst σ)
  | .lam A b => .lam (A.subst σ) (b.tySubst σ)

@[simp] theorem tySubst_id (t : Tm) : t.tySubst Ty.var = t := by
  induction t with
  | bvar | fvar | const => simp [tySubst]
  | app f x ihf ihx => simp only [tySubst, ihf, ihx]
  | lam A b ih => simp only [tySubst, Ty.subst_id, ih]

theorem tySubst_comp (σ τ : Nat → Ty) (t : Tm) :
    (t.tySubst σ).tySubst τ = t.tySubst (fun i => (σ i).subst τ) := by
  induction t with
  | bvar => rfl
  | fvar => simp only [tySubst, Ty.subst_comp]
  | const => simp only [tySubst, Const.tySubst_comp]
  | app f x ihf ihx => simp only [tySubst, ihf, ihx]
  | lam A b ih => simp only [tySubst, Ty.subst_comp, ih]

@[simp] theorem scope_tySubst (σ : Nat → Ty) (d : Nat) (t : Tm) :
    Scope d (t.tySubst σ) ↔ Scope d t := by
  induction t generalizing d with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [tySubst, Scope, ihf, ihx]
  | lam A b ih => exact ih _

@[simp] theorem freeVars_tySubst (σ : Nat → Ty) (t : Tm) :
    (t.tySubst σ).freeVars = t.freeVars.map (fun v => (v.1, v.2.subst σ)) := by
  induction t with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [tySubst, freeVars, ihf, ihx, List.map_append]
  | lam A b ih => exact ih

theorem Scope.mono {d e : Nat} {t : Tm} (h : Scope d t) (hde : d ≤ e) : Scope e t := by
  induction t generalizing d e with
  | bvar i => exact Nat.lt_of_lt_of_le h hde
  | fvar | const => trivial
  | app f x ihf ihx => exact ⟨ihf h.1 hde, ihx h.2 hde⟩
  | lam A b ih => exact ih h (Nat.add_le_add_right hde 1)

end Tm
end Silmaril.Logic.HOLLight
