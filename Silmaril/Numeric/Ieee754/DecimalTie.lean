module

public import Silmaril.Numeric.Ieee754.DecimalSelection

/-! # The formatter's exact decimal-grid tie policy

The parity test applies to integer coefficients on the first successful search
grid. Its unit is `10^(decade(value)-p+1)`, where `p` equals the selected number
of significant digits. This is a statement about that precise grid, not a
claim that arbitrary rescaling leaves coefficient parity invariant.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

/-- The globally minimum significant-digit count selects the actual grid. -/
theorem shortest_candidate_at_significantDigits (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    candidate (roundingInterval bits) (rational bits) (shortest bits).significantDigits = some (shortest bits) := by
  obtain ⟨_, _, _, chosen, equal, _⟩ := shortest_global_minimum bits positive finite
  rwa [equal]

/-- The selected untrimmed coefficient's exponent identifies the common grid
on which the implementation compares parity. -/
theorem shortest_grid_exponent (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    (shortest bits).exponent = decade (rational bits) - ((shortest bits).significantDigits : Int) + 1 := by
  have selected := shortest_candidate_at_significantDigits bits positive finite
  rcases candidate_neighbor _ _ _ selected with equal | equal
  · exact congrArg Number.exponent equal
  · exact congrArg Number.exponent equal

/-- At equal distance from a distinct accepted neighboring grid point, the
selected decimal's coefficient is even. Both sides use the same exponent;
trailing-zero normalization occurs after this comparison. -/
theorem shortest_tie_even_grid_coefficient (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) (number : Number)
    (neighbor : number = lowerNeighbor (rational bits) (shortest bits).significantDigits ∨
      number = upperNeighbor (rational bits) (shortest bits).significantDigits)
    (numberPositive : 0 < number.coefficient)
    (accepted : (roundingInterval bits).accepts number.value = true)
    (different : shortest bits ≠ number)
    (tied : |rational bits - (shortest bits).value| = |rational bits - number.value|) :
    (shortest bits).coefficient % 2 = 0 := by
  have preference := candidate_neighbor_preference (roundingInterval bits) (rational bits)
    (rational_pos_of_positive_finite bits positive finite) (shortest bits).significantDigits
    (shortest_candidate_at_significantDigits bits positive finite) number neighbor numberPositive accepted
  exact (preference.2 tied).resolve_right different

end Silmaril.Numeric.Ieee754.Decimal
