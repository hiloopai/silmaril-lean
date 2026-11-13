module

public import Silmaril.Raw.SSA.Isotope.Refinement.Quantities
public import Silmaril.Raw.SSA.Isotope.Refinement.Polarity

/-!
# Directed effect systems of the written refinement calculus

These are exactly the data in the paper's effect-system definition: bounded
joins, upward-closed iterative effects, two antitone multiplicity allowances,
and a directed mover relation downward-closed in both effects. Purity allows
both mover directions and all quantities. It does not imply iterability:
iterating a total pure computation can introduce divergence.
-/

@[expose] public section

namespace Silmaril.Isotope.Refinement

universe u

/-- An effect system with directed weakening, contraction, and commutation. -/
class EffectSystem (ε : Type u) extends SemilatticeSup ε, OrderBot ε, OrderTop ε where
  iterable : ε → Prop
  iterable_mono : ∀ {e e' : ε}, e ≤ e' → iterable e → iterable e'
  iterable_top : iterable ⊤
  quantity : Polarity → ε → Quantity
  quantity_antitone : ∀ p, Antitone (quantity p)
  quantity_pure : ∀ p, quantity p ⊥ = ⊤
  rightMover : ε → ε → Prop
  rightMover_antitone : ∀ {e e' η η' : ε}, e' ≤ e → η' ≤ η →
    rightMover e η → rightMover e' η'
  pure_rightMover : ∀ e : ε, rightMover ⊥ e
  rightMover_pure : ∀ e : ε, rightMover e ⊥

namespace EffectSystem

variable {ε : Type u} [EffectSystem ε]

/-- Polarity switches right movers to left movers for reversed rewrites. -/
def moves (p : Polarity) (e η : ε) : Prop := p.orient rightMover e η

/-- Commuting effects admit both reorderings. -/
def commutes (e η : ε) : Prop := rightMover e η ∧ rightMover η e

/-- Positive allowance controls deletion, negative allowance introduction. -/
def canDelete (p : Polarity) (e : ε) : Prop := Quantity.affine ≤ quantity p e

/-- Positive allowance controls duplication, negative allowance fusion. -/
def canCopy (p : Polarity) (e : ε) : Prop := Quantity.relevant ≤ quantity p e

@[simp] theorem moves_positive (e η : ε) : moves .positive e η ↔ rightMover e η := Iff.rfl
@[simp] theorem moves_negative (e η : ε) : moves .negative e η ↔ rightMover η e := Iff.rfl
@[simp] theorem moves_reverse (p : Polarity) (e η : ε) :
    moves p.reverse e η ↔ moves p η e := by cases p <;> exact Iff.rfl

theorem moves_antitone (p : Polarity) {e e' η η' : ε} (he : e' ≤ e) (hη : η' ≤ η)
    (h : moves p e η) : moves p e' η' := by
  cases p with
  | positive => exact rightMover_antitone he hη h
  | negative => exact rightMover_antitone hη he h

@[simp] theorem pure_moves (p : Polarity) (e : ε) : moves p ⊥ e := by
  cases p with
  | positive => exact pure_rightMover e
  | negative => exact rightMover_pure e

@[simp] theorem moves_pure (p : Polarity) (e : ε) : moves p e ⊥ := by
  cases p with
  | positive => exact rightMover_pure e
  | negative => exact pure_rightMover e

theorem commutes_symm {e η : ε} (h : commutes e η) : commutes η e := h.symm

theorem commutes_antitone {e e' η η' : ε} (he : e' ≤ e) (hη : η' ≤ η)
    (h : commutes e η) : commutes e' η' :=
  ⟨rightMover_antitone he hη h.1, rightMover_antitone hη he h.2⟩

@[simp] theorem pure_commutes (e : ε) : commutes ⊥ e :=
  ⟨pure_rightMover e, rightMover_pure e⟩

theorem iterable_sup_left {e : ε} (h : iterable e) (η : ε) : iterable (e ⊔ η) :=
  iterable_mono le_sup_left h

theorem iterable_sup_right (e : ε) {η : ε} (h : iterable η) : iterable (e ⊔ η) :=
  iterable_mono le_sup_right h

theorem canDelete_antitone (p : Polarity) {e e' : ε} (he : e' ≤ e)
    (h : canDelete p e) : canDelete p e' := le_trans h (quantity_antitone p he)

theorem canCopy_antitone (p : Polarity) {e e' : ε} (he : e' ≤ e)
    (h : canCopy p e) : canCopy p e' := le_trans h (quantity_antitone p he)

@[simp] theorem canDelete_pure (p : Polarity) : canDelete p (⊥ : ε) := by
  unfold canDelete
  rw [quantity_pure]
  exact le_top

@[simp] theorem canCopy_pure (p : Polarity) : canCopy p (⊥ : ε) := by
  unfold canCopy
  rw [quantity_pure]
  exact le_top

end EffectSystem

end Silmaril.Isotope.Refinement
