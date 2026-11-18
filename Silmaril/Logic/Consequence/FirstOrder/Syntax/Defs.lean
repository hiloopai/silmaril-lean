module

public import Silmaril.Logic.Institution.Examples.Unsorted

/-!
# Unsorted first-order syntax: renaming, substitution, decidable equality

Operations on the terms and formulas of unsorted first-order logic, in its namespace
(`Silmaril.Logic.Institution.Examples.UFOL`: de Bruijn variables `Fin k`, terms with `Fin n`-indexed
arguments, formulas built from `=`, relations, `⊤`, `¬`, `∧`, `∀`):

* `rename ρ` and `subst σ` act on the free variables; under a binder they lift (`liftRename`,
  `liftSubst`). `shift` adds one unused variable; `inst φ t` substitutes `t` for the innermost
  variable of `φ`.
* `Term.decEq`, `Formula.decEq`: decidable equality, when the symbols of each arity have it.

`Thms` relates them to satisfaction: `holds_rename`, `holds_subst`, `holds_shift`, `holds_inst`.
-/

@[expose] public section

namespace Silmaril.Logic.Institution.Examples.UFOL

variable {Sg : Signature}

/-- Lift a renaming under a binder. -/
def liftRename {k m : ℕ} (ρ : Fin k → Fin m) : Fin (k + 1) → Fin (m + 1) :=
  Fin.cases 0 fun i => (ρ i).succ

namespace Term

/-- Rename the variables of a term. -/
def rename {k m : ℕ} (ρ : Fin k → Fin m) : Term Sg k → Term Sg m
  | .var i => .var (ρ i)
  | .app o args => .app o fun j => (args j).rename ρ

/-- Substitute terms for the variables of a term. -/
def subst {k m : ℕ} (σ : Fin k → Term Sg m) : Term Sg k → Term Sg m
  | .var i => σ i
  | .app o args => .app o fun j => (args j).subst σ

/-- Add one unused variable (the new innermost one). -/
abbrev shift {k : ℕ} (t : Term Sg k) : Term Sg (k + 1) := t.rename Fin.succ

/-- **Decidable equality** of terms. -/
def decEq [∀ n, DecidableEq (Sg.Op n)] {k : ℕ} : (t u : Term Sg k) → Decidable (t = u)
  | .var i, .var j => if h : i = j then .isTrue (h ▸ rfl) else .isFalse fun e => h (Term.var.inj e)
  | .var _, .app .. => .isFalse fun e => nomatch e
  | .app .., .var _ => .isFalse fun e => nomatch e
  | .app (n := n) o a, .app (n := n') o' a' =>
    if hn : n = n' then by
      subst hn
      exact if ho : o = o' then
        have : DecidablePred fun j => a j = a' j := fun j => decEq (a j) (a' j)
        if ha : ∀ j, a j = a' j then .isTrue (by subst ho; exact congrArg _ (funext ha))
        else .isFalse fun e => ha (by cases e; intro j; rfl)
      else .isFalse fun e => ho (by cases e; rfl)
    else .isFalse fun e => hn (by cases e; rfl)

instance [∀ n, DecidableEq (Sg.Op n)] {k : ℕ} : DecidableEq (Term Sg k) := decEq

end Term

/-- Lift a substitution under a binder. -/
def liftSubst {k m : ℕ} (σ : Fin k → Term Sg m) : Fin (k + 1) → Term Sg (m + 1) :=
  Fin.cases (.var 0) fun i => (σ i).shift

namespace Formula

/-- Rename the free variables of a formula. -/
def rename : {k m : ℕ} → (Fin k → Fin m) → Formula Sg k → Formula Sg m
  | _, _, ρ, .eq t u => .eq (t.rename ρ) (u.rename ρ)
  | _, _, ρ, .rel r args => .rel r fun j => (args j).rename ρ
  | _, _, _, .tt => .tt
  | _, _, ρ, .not φ => .not (φ.rename ρ)
  | _, _, ρ, .and φ ψ => .and (φ.rename ρ) (ψ.rename ρ)
  | _, _, ρ, .all φ => .all (φ.rename (liftRename ρ))

/-- Substitute terms for the free variables of a formula. -/
def subst : {k m : ℕ} → (Fin k → Term Sg m) → Formula Sg k → Formula Sg m
  | _, _, σ, .eq t u => .eq (t.subst σ) (u.subst σ)
  | _, _, σ, .rel r args => .rel r fun j => (args j).subst σ
  | _, _, _, .tt => .tt
  | _, _, σ, .not φ => .not (φ.subst σ)
  | _, _, σ, .and φ ψ => .and (φ.subst σ) (ψ.subst σ)
  | _, _, σ, .all φ => .all (φ.subst (liftSubst σ))

/-- Add one unused free variable. -/
abbrev shift {k : ℕ} (φ : Formula Sg k) : Formula Sg (k + 1) := φ.rename Fin.succ

/-- Substitute `t` for the innermost variable. -/
abbrev inst {k : ℕ} (φ : Formula Sg (k + 1)) (t : Term Sg k) : Formula Sg k :=
  φ.subst (Fin.cases t Term.var)

/-- **Decidable equality** of formulas. -/
def decEq [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)] :
    {k : ℕ} → (φ ψ : Formula Sg k) → Decidable (φ = ψ)
  | _, .eq t u, .eq t' u' =>
    if h : t = t' ∧ u = u' then .isTrue (by rw [h.1, h.2])
    else .isFalse fun e => h (by cases e; exact ⟨rfl, rfl⟩)
  | _, .rel (n := n) r a, .rel (n := n') r' a' =>
    if hn : n = n' then by
      subst hn
      exact if h : r = r' ∧ ∀ j, a j = a' j then .isTrue (by rw [h.1, funext h.2])
        else .isFalse fun e => h (by cases e; exact ⟨rfl, fun _ => rfl⟩)
    else .isFalse fun e => hn (by cases e; rfl)
  | _, .tt, .tt => .isTrue rfl
  | _, .not φ, .not φ' =>
    match decEq φ φ' with
    | .isTrue h => .isTrue (h ▸ rfl)
    | .isFalse h => .isFalse fun e => h (Formula.not.inj e)
  | _, .and φ ψ, .and φ' ψ' =>
    match decEq φ φ', decEq ψ ψ' with
    | .isTrue h₁, .isTrue h₂ => .isTrue (h₁ ▸ h₂ ▸ rfl)
    | .isFalse h, _ => .isFalse fun e => h (Formula.and.inj e).1
    | _, .isFalse h => .isFalse fun e => h (Formula.and.inj e).2
  | _, .all φ, .all φ' =>
    match decEq φ φ' with
    | .isTrue h => .isTrue (h ▸ rfl)
    | .isFalse h => .isFalse fun e => h (Formula.all.inj e)
  | _, .eq .., .rel .. | _, .eq .., .tt | _, .eq .., .not _ | _, .eq .., .and .. | _, .eq .., .all _
  | _, .rel .., .eq .. | _, .rel .., .tt | _, .rel .., .not _ | _, .rel .., .and .. | _, .rel .., .all _
  | _, .tt, .eq .. | _, .tt, .rel .. | _, .tt, .not _ | _, .tt, .and .. | _, .tt, .all _
  | _, .not _, .eq .. | _, .not _, .rel .. | _, .not _, .tt | _, .not _, .and .. | _, .not _, .all _
  | _, .and .., .eq .. | _, .and .., .rel .. | _, .and .., .tt | _, .and .., .not _ | _, .and .., .all _
  | _, .all _, .eq .. | _, .all _, .rel .. | _, .all _, .tt | _, .all _, .not _ | _, .all _, .and .. =>
    .isFalse fun e => nomatch e

instance [∀ n, DecidableEq (Sg.Op n)] [∀ n, DecidableEq (Sg.Rel n)] {k : ℕ} :
    DecidableEq (Formula Sg k) := decEq

end Formula

end Silmaril.Logic.Institution.Examples.UFOL
