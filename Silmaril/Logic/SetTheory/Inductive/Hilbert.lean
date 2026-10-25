module

public import Silmaril.Logic.SetTheory.Inductive.Named
public import Silmaril.Logic.SetTheory.Inductive.Classical

@[expose] public section

/-!
# Independent proof-relevant Hilbert fragment

The implication/negation rules are defined directly on finite formulas, without
native trees, substitutions or semantic premises. The extra theory is a set of
finite formulas. Quantified membership formulas may occur as atoms of these
propositional inferences. `toClassical` builds independent natural-deduction
objects; it is not a completeness argument for quantifier inferences.
-/

namespace Silmaril.Logic.SetTheory.Inductive.Named


/-- A small independent classical Hilbert presentation. -/
inductive Hilbert {V : Type*} (Ax : Set (Formula V)) (Γ : List (Formula V)) : Formula V → Type _
  | hyp {p} (h : p ∈ Γ) : Hilbert Ax Γ p
  | ax {p} (h : p ∈ Ax) : Hilbert Ax Γ p
  | k (p q) : Hilbert Ax Γ (.imp p (.imp q p))
  | s (p q r) : Hilbert Ax Γ (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)))
  | c (p q) : Hilbert Ax Γ (.imp (.imp (.neg p) (.neg q)) (.imp q p))
  | mp {p q} : Hilbert Ax Γ (.imp p q) → Hilbert Ax Γ p → Hilbert Ax Γ q

namespace Hilbert

/-- Finite syntactic support of an inference object, including intermediate formulas. -/
def vars {V : Type*} {Ax : Set (Formula V)} {Γ : List (Formula V)} :
    {p : Formula V} → Hilbert Ax Γ p → List V
  | _, .hyp (p := p) _ => p.vars
  | _, .ax (p := p) _ => p.vars
  | _, .k p q | _, .c p q => p.vars ++ q.vars
  | _, .s p q r => p.vars ++ q.vars ++ r.vars
  | _, .mp di dp => vars di ++ vars dp

/-- The conclusion's names occur in its proof's finite support. -/
theorem conclusion_vars {V : Type*} {Ax : Set (Formula V)} {Γ : List (Formula V)}
    {p : Formula V} (d : Hilbert Ax Γ p) : ∀ v ∈ p.vars, v ∈ d.vars := by
  induction d with
  | hyp _ | ax _ => exact fun _ h => h
  | k p q | c p q => simp [Formula.vars, vars]; tauto
  | s p q r => simp [Formula.vars, vars]; tauto
  | mp di dp ih ip =>
    intro v hv
    exact List.mem_append_left _ (ih v (List.mem_append_right _ hv))

/-- A multi-step proof of identity in the independent Hilbert calculus. -/
def identity {V : Type*} {Ax : Set (Formula V)} {Γ : List (Formula V)} (p : Formula V) :
    Hilbert Ax Γ (.imp p p) :=
  .mp (.mp (.s p (.imp p p) p) (.k p (.imp p p))) (.k p p)

/-- Transport Hilbert proofs into scoped natural-deduction inference objects. -/
noncomputable def toClassical {V : Type*} [DecidableEq V] {n : Nat}
    {Ax : Set (Formula V)} {Bx : Classical.AxiomFamily} {Γ : List (Formula V)}
    (ρ : V → Fin n)
    (hAx : ∀ p ∈ Ax, Classical.Derivation Bx (Γ.map (Formula.lower ρ)) (p.lower ρ))
    {p : Formula V} (d : Hilbert Ax Γ p) :
    Classical.Derivation Bx (Γ.map (Formula.lower ρ)) (p.lower ρ) := by
  induction d with
  | hyp hp => exact .hyp (List.mem_map.mpr ⟨_, hp, rfl⟩)
  | ax hp => exact hAx _ hp
  | k p q => exact .impI (.impI (.hyp (by simp)))
  | s p q r =>
    exact .impI (.impI (.impI (.impE (p := q.lower ρ)
      (.impE (p := p.lower ρ) (.hyp (by simp [Formula.lower])) (.hyp (by simp [Formula.lower])))
      (.impE (p := p.lower ρ) (.hyp (by simp [Formula.lower])) (.hyp (by simp [Formula.lower]))))))
  | c p q =>
    exact .impI (.impI (.dne (.negI (.negE (p := q.lower ρ)
      (.impE (p := .neg (p.lower ρ)) (.hyp (by simp [Formula.lower])) (.hyp (by simp [Formula.lower])))
      (.hyp (by simp [Formula.lower]))))))
  | mp _ _ ih ip => exact .impE ih ip

/-- Propositional soundness in any membership structure. -/
theorem sound {M V : Type*} [Membership M M] [DecidableEq V]
    {Ax : Set (Formula V)} {Γ : List (Formula V)}
    (hAx : ∀ p ∈ Ax, ∀ E : V → M, p.eval E)
    {p : Formula V} (d : Hilbert Ax Γ p) (E : V → M) (hΓ : ∀ q ∈ Γ, q.eval E) : p.eval E := by
  induction d with
  | hyp hp => exact hΓ _ hp
  | ax hp => exact hAx _ hp E
  | k p q => exact fun hp _ => hp
  | s p q r => exact fun h hr hp => h hp (hr hp)
  | c p q =>
    classical
    exact fun h hq => by_contra fun hp => h hp hq
  | mp _ _ ih ip => exact ih ip

end Hilbert
end Silmaril.Logic.SetTheory.Inductive.Named
