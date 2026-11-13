module

public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# The quantities of the written refinement calculus

The paper's nonzero quantities form the four-element lattice `Quantity`.
Its extended quantities `Usage` add an incomparable zero below affine and
unrestricted usage, giving a join-semilattice but no bottom and no meet for
every pair. Multiplication extends nonzero meet by an absorbing zero.

This multiplication is intentionally not a semiring multiplication: it does
not distribute over extended joins. `Usage.mul_sup_counterexample` records the
distinction. These definitions follow `complete-refinement-ssa.tex`, variable
quantities and context weakening (lines 729–818 at thesis commit 3691b30).
-/

@[expose] public section

namespace Silmaril.Isotope.Refinement

/-- Nonzero allowances: exactly once, at least once, at most once, unrestricted. -/
inductive Quantity where
  | linear
  | relevant
  | affine
  | unrestricted
  deriving DecidableEq, Repr

namespace Quantity

def le : Quantity → Quantity → Prop
  | .linear, _ => True
  | _, .unrestricted => True
  | .relevant, .relevant => True
  | .affine, .affine => True
  | _, _ => False

instance : LE Quantity := ⟨le⟩
instance : DecidableLE Quantity := by
  intro a b
  change Decidable (le a b)
  cases a <;> cases b <;> simp only [le] <;> infer_instance

instance : PartialOrder Quantity where
  le_refl := by intro a; cases a <;> decide
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_antisymm := by intro a b; cases a <;> cases b <;> decide

def join : Quantity → Quantity → Quantity
  | .linear, b => b
  | a, .linear => a
  | .relevant, .relevant => .relevant
  | .affine, .affine => .affine
  | _, _ => .unrestricted

def meet : Quantity → Quantity → Quantity
  | .unrestricted, b => b
  | a, .unrestricted => a
  | .relevant, .relevant => .relevant
  | .affine, .affine => .affine
  | _, _ => .linear

instance : DistribLattice Quantity where
  sup := join
  inf := meet
  le_sup_left := by intro a b; cases a <;> cases b <;> decide
  le_sup_right := by intro a b; cases a <;> cases b <;> decide
  sup_le := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  inf_le_left := by intro a b; cases a <;> cases b <;> decide
  inf_le_right := by intro a b; cases a <;> cases b <;> decide
  le_inf := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_sup_inf := by intro a b c; cases a <;> cases b <;> cases c <;> decide

instance : BoundedOrder Quantity where
  top := .unrestricted
  bot := .linear
  le_top := by intro a; cases a <;> decide
  bot_le := by intro a; cases a <;> decide

@[simp] theorem top_eq : (⊤ : Quantity) = .unrestricted := rfl
@[simp] theorem bot_eq : (⊥ : Quantity) = .linear := rfl
@[simp] theorem relevant_inf_affine : relevant ⊓ affine = linear := rfl
@[simp] theorem relevant_sup_affine : relevant ⊔ affine = unrestricted := rfl

instance : Fintype Quantity where
  elems := {.linear, .relevant, .affine, .unrestricted}
  complete := by intro a; cases a <;> simp

end Quantity

/-- Extended usage allowances include using a variable zero times. -/
inductive Usage where
  | zero
  | used (quantity : Quantity)
  deriving DecidableEq, Repr

namespace Usage

instance : Fintype Usage where
  elems := {.zero, .used .linear, .used .relevant, .used .affine, .used .unrestricted}
  complete := by
    intro a
    cases a with
    | zero => simp
    | used a => cases a <;> simp

instance : Coe Quantity Usage := ⟨used⟩
instance : Zero Usage := ⟨zero⟩

def le : Usage → Usage → Prop
  | .zero, .zero => True
  | .zero, .used .affine => True
  | .zero, .used .unrestricted => True
  | .used a, .used b => a ≤ b
  | _, _ => False

instance : LE Usage := ⟨le⟩
instance : DecidableLE Usage := by
  intro a b
  change Decidable (le a b)
  cases a with
  | zero => cases b with
    | zero => exact inferInstanceAs (Decidable True)
    | used b => cases b <;> simp only [le] <;> infer_instance
  | used a => cases b with
    | zero => exact inferInstanceAs (Decidable False)
    | used b => exact inferInstanceAs (Decidable (a ≤ b))

instance : PartialOrder Usage where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

def join : Usage → Usage → Usage
  | .zero, .zero => .zero
  | .zero, .used .linear => .used .affine
  | .used .linear, .zero => .used .affine
  | .zero, .used .relevant => .used .unrestricted
  | .used .relevant, .zero => .used .unrestricted
  | .zero, .used q => .used q
  | .used q, .zero => .used q
  | .used a, .used b => .used (a ⊔ b)

instance : SemilatticeSup Usage where
  sup := join
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : OrderTop Usage where
  top := .used .unrestricted
  le_top := by decide

@[simp] theorem used_le_used (a b : Quantity) : used a ≤ used b ↔ a ≤ b := Iff.rfl
@[simp] theorem zero_le_used (a : Quantity) : zero ≤ used a ↔ Quantity.affine ≤ a := by
  cases a <;> decide
@[simp] theorem not_used_le_zero (a : Quantity) : ¬ used a ≤ zero := by intro h; exact h
@[simp] theorem top_eq : (⊤ : Usage) = .used .unrestricted := rfl

/-- The paper's extended meet has an absorbing zero. -/
def mul : Usage → Usage → Usage
  | .zero, _ => .zero
  | _, .zero => .zero
  | .used a, .used b => .used (a ⊓ b)

instance : Mul Usage := ⟨mul⟩

@[simp] theorem zero_mul (a : Usage) : zero * a = zero := rfl
@[simp] theorem mul_zero (a : Usage) : a * zero = zero := by cases a <;> rfl
@[simp] theorem used_mul_used (a b : Quantity) : used a * used b = used (a ⊓ b) := rfl
theorem mul_comm (a b : Usage) : a * b = b * a := by
  cases a <;> cases b <;> simp [inf_comm]
theorem mul_assoc (a b c : Usage) : (a * b) * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [inf_assoc]
@[simp] theorem mul_unrestricted (a : Usage) : a * used .unrestricted = a := by
  cases a with
  | zero => rfl
  | used a => cases a <;> rfl
@[simp] theorem unrestricted_mul (a : Usage) : used .unrestricted * a = a := by
  rw [mul_comm, mul_unrestricted]

/-- Effective use allowance of a variable with the specified type linearity. -/
def effective (q : Usage) (A : Quantity) : Usage := q * used A

/-- An unused variable imposes no restriction on the context's linearity. -/
def linearity : Usage → Quantity → Quantity
  | .zero, _ => .unrestricted
  | .used q, A => A ⊓ q

@[simp] theorem effective_zero (A : Quantity) : effective zero A = zero := rfl
@[simp] theorem effective_used (q A : Quantity) : effective (used q) A = used (q ⊓ A) := rfl
@[simp] theorem linearity_zero (A : Quantity) : linearity zero A = .unrestricted := rfl
@[simp] theorem linearity_used (q A : Quantity) : linearity (used q) A = A ⊓ q := rfl

/-- The linearity of an unused slot permits every quantity; otherwise it is
exactly the effective nonzero usage bound. -/
theorem le_linearity_iff (q : Quantity) (u : Usage) (A : Quantity) :
    q ≤ linearity u A ↔ u = zero ∨ used q ≤ effective u A := by decide +revert

/-- A nonzero allowance can be used effectively only when the slot is present. -/
theorem used_le_effective_iff (q : Quantity) (u : Usage) (A : Quantity) :
    used q ≤ effective u A ↔ q ≤ linearity u A ∧ u ≠ zero := by decide +revert

@[simp] theorem effective_linear (A : Quantity) :
    effective (used .linear) A = used .linear := by decide +revert

/-- An unused slot is unrestricted and can always be discarded. -/
theorem zero_le_effective_iff (u : Usage) (A : Quantity) :
    zero ≤ effective u A ↔ Quantity.affine ≤ linearity u A := by decide +revert

theorem relevant_le_effective_iff (u : Usage) (A : Quantity) :
    used .relevant ≤ effective u A ↔ Quantity.relevant ≤ linearity u A ∧ u ≠ zero :=
  used_le_effective_iff .relevant u A

@[simp] theorem effective_idem (u : Usage) (A : Quantity) :
    effective (effective u A) A = effective u A := by decide +revert

@[simp] theorem linearity_effective (u : Usage) (A : Quantity) :
    linearity (effective u A) A = linearity u A := by decide +revert

/-- Context weakening compares effective allowances; multiplication itself
does not preserve the extended quantity order. -/
theorem effective_not_monotone :
    ¬ Monotone (fun u : Usage => effective u .relevant) := by
  intro h
  have hbad := h (show zero ≤ used .affine from trivial)
  exact hbad

/-- Zero and exactly-once usage have no common lower bound. -/
theorem no_lower_bound_zero_linear : ¬ ∃ q : Usage, q ≤ zero ∧ q ≤ used .linear := by
  rintro ⟨q, h, k⟩
  cases q with
  | zero => exact k
  | used q => exact h

/-- Extended multiplication is not distributive, so these quantities are not a semiring. -/
theorem mul_sup_counterexample :
    (zero ⊔ used .linear) * used .relevant ≠
      (zero * used .relevant) ⊔ (used .linear * used .relevant) := by decide

end Usage

end Silmaril.Isotope.Refinement
