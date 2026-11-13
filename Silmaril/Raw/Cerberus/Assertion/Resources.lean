module

public import Silmaril.Cerberus.Assertion.Pure.Defs

/-! A finite, abstract, whole-cell ownership fragment for CN-style assertions.
Addresses are natural numbers and cells contain mathematical integers. This is not
Cerberus's allocation/provenance memory, fractional ownership or CN's resource model.
A concrete-memory interpretation and its adequacy proof remain separate obligations.
Heaps are finite association lists; separating conjunction ignores enumeration order. -/

@[expose] public section
namespace Silmaril.Cerberus.Assertion.Resources

abbrev Heap := List (Nat × Int)

def Disjoint (h₁ h₂ : Heap) : Prop :=
  ∀ a v₁ v₂, (a, v₁) ∈ h₁ → (a, v₂) ∈ h₂ → False

inductive Formula where
  | emp
  | pure : Pure.Formula → Formula
  | pointsTo : Nat → Pure.Term → Formula
  | sep : Formula → Formula → Formula
  deriving Repr, DecidableEq

/-- Pure assertions consume no heap; spatial cells grant exclusive ownership. -/
def Formula.holds (ρ : Pure.Env) : Formula → Heap → Prop
  | .emp, h => h = []
  | .pure p, h => h = [] ∧ p.holds ρ
  | .pointsTo a v, h => h = [(a, v.eval ρ)]
  | .sep p q, h => ∃ h₁ h₂, Disjoint h₁ h₂ ∧ h.Perm (h₁ ++ h₂) ∧
      p.holds ρ h₁ ∧ q.holds ρ h₂

/-- A Lean obligation with executable pure leaves and explicit resource witnesses.
No search or decision procedure for resource splitting is assumed. -/
def Formula.leanGoal (ρ : Pure.Env) : Formula → Heap → Prop
  | .emp, h => h = []
  | .pure p, h => h = [] ∧ p.check ρ = true
  | .pointsTo a v, h => h = [(a, v.eval ρ)]
  | .sep p q, h => ∃ h₁ h₂, Disjoint h₁ h₂ ∧ h.Perm (h₁ ++ h₂) ∧
      p.leanGoal ρ h₁ ∧ q.leanGoal ρ h₂

theorem Formula.leanGoal_correct (ρ : Pure.Env) (p : Formula) (h : Heap) :
    p.leanGoal ρ h ↔ p.holds ρ h := by
  induction p generalizing h <;>
    simp_all [leanGoal, holds, Pure.Formula.check_correct]

theorem pure_embedding (ρ : Pure.Env) (p : Pure.Formula) :
    (Formula.pure p).holds ρ [] ↔ p.holds ρ := by
  simp [Formula.holds]

/-- Two full permissions to the same address cannot be separated. -/
theorem duplicate_ownership_impossible (ρ : Pure.Env) (a : Nat)
    (v w : Pure.Term) (h : Heap) :
    ¬(Formula.sep (.pointsTo a v) (.pointsTo a w)).holds ρ h := by
  rintro ⟨h₁, h₂, hd, _, hv, hw⟩
  change h₁ = [(a, v.eval ρ)] at hv
  change h₂ = [(a, w.eval ρ)] at hw
  subst h₁
  subst h₂
  exact hd a (v.eval ρ) (w.eval ρ) (by simp) (by simp)

/-- Ownership of distinct cells has a concrete finite witness. -/
theorem two_cells (ρ : Pure.Env) (a b : Nat) (v w : Pure.Term) (hab : a ≠ b) :
    (Formula.sep (.pointsTo a v) (.pointsTo b w)).holds ρ
      [(a, v.eval ρ), (b, w.eval ρ)] := by
  refine ⟨[(a, v.eval ρ)], [(b, w.eval ρ)], ?_, .refl _, rfl, rfl⟩
  intro c x y hx hy
  simp only [List.mem_singleton, Prod.mk.injEq] at hx hy
  exact hab (hx.1.symm.trans hy.1)

end Silmaril.Cerberus.Assertion.Resources
