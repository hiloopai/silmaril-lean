module

public import Silmaril.Numeric.Ieee754.DecimalRounding
public import Silmaril.Numeric.Ieee754.Binary64Signs
public import Silmaril.Numeric.DecimalText
import Mathlib.Tactic.Linarith

/-! # Signed exact rational conversion and decimal parsing

Rounding uses the proved nearest-even magnitude converter, then reattaches the
sign without altering magnitude bits. A separate sign argument retains negative
zero; ordinary rationals use a positive zero sign.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.RationalRounding

open Binary64Signs

def roundSigned (negative : Bool) (magnitude : ℚ) : UInt64 :=
  withSign negative (roundPositive magnitude)

def roundRational (query : ℚ) : UInt64 := roundSigned (decide (query < 0)) |query|

/-- Convert an exact finite decimal, retaining its zero sign. -/
def roundFinite (value : DecimalText.Finite) : UInt64 := roundSigned value.negative value.magnitude

/-- Parse the complete decimal string and convert once, using exact rational
arithmetic. NaN text produces the standard quiet NaN encoding. -/
def parseBinary64 (text : String) : Option UInt64 :=
  (DecimalText.parse text).map fun value => match value with
    | .finite value => roundFinite value
    | .infinity negative => withSign negative 0x7ff0000000000000
    | .nan => 0x7ff8000000000000

@[simp] theorem roundPositive_zero : roundPositive 0 = 0 := by
  obtain ⟨_, nearest, _⟩ := roundIndex_nearestEven 0 (by rfl) overflowThreshold_pos
  have distance := nearest 0
  simp only [magnitude_zero, sub_zero, abs_zero, zero_sub, abs_neg] at distance
  have zero : magnitude (roundIndex 0) = 0 := abs_nonpos_iff.mp distance
  have index : roundIndex 0 = 0 := magnitude_strictMono.injective (by rwa [magnitude_zero])
  apply UInt64.toNat_inj.mp
  rw [roundPositive_toNat, index]
  rfl

/-- Every signed conversion uses precisely the proved magnitude result,
including overflow. -/
theorem magnitudeBits_roundSigned (negative : Bool) (query : ℚ) :
    magnitudeBits (roundSigned negative query) = roundPositive query := by
  rw [roundSigned, magnitudeBits_withSign]
  apply UInt64.toNat_inj.mp
  rw [magnitudeBits_toNat, roundPositive_toNat]
  apply Nat.mod_eq_of_lt
  have bounded := roundIndex_le_limit query
  unfold limit at bounded
  norm_num at bounded ⊢
  omega

/-- The returned encoding carries the requested sign, including when the
rounded magnitude is zero or infinity. -/
theorem signBit_roundSigned (negative : Bool) (query : ℚ) :
    (F64.ofBits (roundSigned negative query)).signBit = negative := by
  apply signBit_withSign
  have clear := magnitudeBits_roundSigned false query
  exact clear

/-- Explicit sign reattachment turns any magnitude round-trip into a signed
round-trip, including a separately represented negative zero. -/
theorem roundSigned_of_magnitude (bits : UInt64) (query : ℚ)
    (rounded : roundPositive query = magnitudeBits bits) :
    roundSigned (F64.ofBits bits).signBit query = bits := by
  rw [roundSigned, rounded, withSign_magnitudeBits]

@[simp] theorem roundSigned_zero (negative : Bool) :
    roundSigned negative 0 = if negative then 0x8000000000000000 else 0 := by
  rw [roundSigned, roundPositive_zero]
  cases negative <;> rfl

/-- Signed conversion satisfies the same global nearest-even magnitude law;
the returned sign is handled separately, so negative zero is never erased. -/
theorem roundSigned_nearestEven (negative : Bool) (query : ℚ) (nonnegative : 0 ≤ query)
    (below : query < overflowThreshold) :
    (magnitudeBits (roundSigned negative query)).toNat < limit ∧
      AdjacentRounding.NearestEven magnitude query (magnitudeBits (roundSigned negative query)).toNat := by
  rw [magnitudeBits_roundSigned, roundPositive_toNat]
  exact roundIndex_nearestEven query nonnegative below

end Silmaril.Numeric.Ieee754.RationalRounding
