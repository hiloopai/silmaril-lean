module

public import Silmaril.Raw.SSA.Isotope.Morphism.IterSSA
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ScopeStructural

/-!
# Scope and typing of the identity variable assignment

The round-trip theorems compile closed-variable let-iter terms whose bound
variables are already positional. The assignment used there is the identity:
source bound variable `i` is target variable `i`, and there are no free
variables. This module records that assignment, the bound it satisfies, and the
fact that compilation under a bounded assignment produces a scoped region.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.IterSSA

open LetIter.LocallyNameless (Tm)
open LambdaSSA (Region)

variable {ν : Type w} {Φ : Type v} {τ : Type u} {n : Nat}

namespace Vars

/-- Every mapped source variable lands inside the first `m` target variables. -/
structure Bounded (vars : Vars ν n) (m : Nat) : Prop where
  /-- Free source variables are mapped below the bound. -/
  free : ∀ x, vars.free x < m
  /-- Bound source variables are mapped below the bound. -/
  bound : ∀ i, vars.bound i < m

/-- The assignment sending bound variable `i` to target variable `i`. A
positional source term has no free variables, so none need a target slot. -/
def identity (n : Nat) : Vars Empty n := ⟨Empty.elim, fun i => i.val⟩

@[simp] theorem identity_bound (n : Nat) (i : Fin n) : (identity n).bound i = i.val := rfl

/-- The identity assignment stays inside the ambient positional context. -/
theorem identity_bounded (n : Nat) : (identity n).Bounded n :=
  ⟨fun x => x.elim, fun i => i.isLt⟩

/-- An administrative target binder keeps the bound, shifted by one. -/
theorem Bounded.shift {vars : Vars ν n} {m : Nat} (h : vars.Bounded m) :
    vars.shift.Bounded (m + 1) :=
  ⟨fun x => Nat.succ_lt_succ (h.free x), fun i => Nat.succ_lt_succ (h.bound i)⟩

/-- A common source and target binder keeps the bound, shifted by one. -/
theorem Bounded.bind {vars : Vars ν n} {m : Nat} (h : vars.Bounded m) :
    vars.bind.Bounded (m + 1) :=
  ⟨fun x => Nat.succ_lt_succ (h.free x),
    Fin.cases (Nat.zero_lt_succ _) (fun i => Nat.succ_lt_succ (h.bound i))⟩

/-- The identity assignment types every bound variable at its own slot. -/
theorem identity_hasType (β : BoundCtx τ n) :
    Vars.HasType (ν := Empty) .nil β β.toList (identity n) where
  free := fun x _ => x.elim
  bound i := β.getElem?_toList i

end Vars

/-- Compilation under a bounded assignment produces a region scoped by the same
variable bound, provided the continuation is scoped under the result binder. -/
theorem under_scoped {k : Region Φ} {labels m : Nat} (hk : k.Scoped labels (m + 1)) :
    (under k).Scoped labels (m + 2) :=
  hk.renameVars (fun i hi => by cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ j => exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.lt_of_succ_lt_succ hi)))

/-- Compilation under a bounded assignment produces a region scoped by the same
variable bound, provided the continuation is scoped under the result binder. -/
theorem compile_scoped {t : Tm ν Φ n} {vars : Vars ν n} {k : Region Φ} {labels m : Nat}
    (hv : vars.Bounded m) (hk : k.Scoped labels (m + 1)) :
    (compile t vars k).Scoped labels m := by
  induction t generalizing k labels m with
  | fv x => exact ⟨hv.free x, hk⟩
  | bv i => exact ⟨hv.bound i, hk⟩
  | unit => exact ⟨trivial, hk⟩
  | op f a ih => exact ih hv ⟨Nat.zero_lt_succ _, under_scoped hk⟩
  | pair a b iha ihb =>
      exact iha hv (ihb hv.shift
        ⟨⟨Nat.succ_lt_succ (Nat.zero_lt_succ _), Nat.zero_lt_succ _⟩,
          under_scoped (under_scoped hk)⟩)
  | let₁ a b iha ihb => exact iha hv (ihb hv.bind (under_scoped hk))
  | let₂ a b iha ihb =>
      exact iha hv ⟨Nat.zero_lt_succ _,
        ihb hv.shift.bind.bind (under_scoped (under_scoped (under_scoped hk)))⟩
  | inl a ih => exact ih hv ⟨Nat.zero_lt_succ _, under_scoped hk⟩
  | inr a ih => exact ih hv ⟨Nat.zero_lt_succ _, under_scoped hk⟩
  | case a l r iha ihl ihr =>
      exact iha hv ⟨Nat.zero_lt_succ _,
        ihl hv.shift.bind (under_scoped (under_scoped hk)),
        ihr hv.shift.bind (under_scoped (under_scoped hk))⟩
  | abort a ih => exact ih hv ⟨Nat.zero_lt_succ _, under_scoped hk⟩
  | iter init body ihInit ihBody =>
      refine ⟨ihInit hv ⟨by omega, Nat.zero_lt_succ _⟩, fun _ => ihBody hv.bind ?_⟩
      exact ⟨Nat.zero_lt_succ _,
        under_scoped (under_scoped (hk.renameLabels (fun i hi => by omega))),
        ⟨by omega, Nat.zero_lt_succ _⟩⟩

/-- Compiling a positional term with a returning continuation gives a region
with exactly one exit label. -/
theorem compile_return_scoped (t : Tm Empty Φ n) :
    (compile t (Vars.identity n) (.br 0 (.var 0))).Scoped 1 n :=
  compile_scoped (Vars.identity_bounded n) ⟨Nat.zero_lt_one, Nat.zero_lt_succ _⟩

end Silmaril.Isotope.Morphism.IterSSA
