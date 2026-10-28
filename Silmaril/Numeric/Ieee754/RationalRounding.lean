module

public import Silmaril.Numeric.Ieee754.BinaryMagnitudeOrder
public import Silmaril.Numeric.Ieee754.AdjacentRounding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exact rational-to-binary64 conversion

A finite bisection finds adjacent positive magnitudes; an exact midpoint test
chooses the nearest, breaking ties by the encoding's even low bit. Overflow
uses the midpoint between maximum finite and the virtual value `2^1024`, with
the tie rounding to infinity. The independent correctness predicate quantifies
over all binary magnitudes and includes the parity condition.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.RationalRounding

/-- The unsigned infinity encoding, also the first virtual overflow magnitude. -/
def limit : Nat := 0x7ff0000000000000

def magnitude : Nat → ℚ := BinaryMagnitude.value 52 1023

def overflowThreshold : ℚ := (magnitude (limit - 1) + magnitude limit) / 2

/-- The virtual endpoint is the first magnitude beyond finite binary64. -/
theorem magnitude_limit : magnitude limit = (2 : ℚ) ^ (1024 : Nat) := by
  norm_num [magnitude, limit, BinaryMagnitude.value, BinaryMagnitude.significand,
    BinaryMagnitude.radix, BinaryMagnitude.spacing]
  change (4503599627370496 : ℚ) * 2 ^ (972 : Nat) = 2 ^ (1024 : Nat)
  rw [show (1024 : Nat) = 52 + 972 from rfl, pow_add]
  norm_num

/-- IEEE nearest-even overflow occurs halfway from maximum finite to `2^1024`. -/
theorem overflowThreshold_value : overflowThreshold = (2 : ℚ) ^ (1024 : Nat) - 2 ^ (970 : Nat) := by
  norm_num [overflowThreshold, magnitude, limit, BinaryMagnitude.value,
    BinaryMagnitude.significand, BinaryMagnitude.radix, BinaryMagnitude.spacing]
  change ((9007199254740991 : ℚ) * 2 ^ (971 : Nat) + 4503599627370496 * 2 ^ (972 : Nat)) / 2 =
    2 ^ (1024 : Nat) - 2 ^ (970 : Nat)
  rw [show (971 : Nat) = 970 + 1 from rfl, pow_add,
    show (972 : Nat) = 970 + 2 from rfl, pow_add,
    show (1024 : Nat) = 970 + 54 from rfl, pow_add]
  norm_num
  generalize (2 : ℚ) ^ (970 : Nat) = unit
  ring

theorem magnitude_strictMono : StrictMono magnitude := BinaryMagnitude.value_strictMono 52 1023

@[simp] theorem magnitude_zero : magnitude 0 = 0 := BinaryMagnitude.value_zero 52 1023

theorem overflowThreshold_lt_limit : overflowThreshold < magnitude limit := by
  have less := magnitude_strictMono (show limit - 1 < limit by decide)
  unfold overflowThreshold
  linarith

theorem maxFinite_lt_overflowThreshold : magnitude (limit - 1) < overflowThreshold := by
  have less := magnitude_strictMono (show limit - 1 < limit by decide)
  unfold overflowThreshold
  linarith

theorem overflowThreshold_pos : 0 < overflowThreshold := by
  have positive := BinaryMagnitude.value_pos 52 1023 (limit - 1) (by decide)
  exact lt_trans positive maxFinite_lt_overflowThreshold

/-- Conversion of a nonnegative magnitude. Negative inputs are assigned zero;
the correctness theorem below states the intended nonnegative domain. -/
def roundIndex (query : ℚ) : Nat :=
  if query < 0 then 0
  else if overflowThreshold ≤ query then limit
  else AdjacentRounding.choose magnitude query (Bisection.lastLE magnitude query 0 limit)

/-- Actual binary64 interchange output, with positive infinity on overflow. -/
def roundPositive (query : ℚ) : UInt64 := UInt64.ofNat (roundIndex query)

theorem bracket_spec (query : ℚ) (nonnegative : 0 ≤ query) (below : query < overflowThreshold) :
    let lower := Bisection.lastLE magnitude query 0 limit
    lower < limit ∧ magnitude lower ≤ query ∧ query < magnitude (lower + 1) := by
  have bracket := Bisection.lastLE_spec magnitude query 0 limit (by decide)
    (by simpa only [magnitude_zero] using nonnegative) (below.trans overflowThreshold_lt_limit)
  exact bracket.2

/-- A query below the overflow midpoint cannot select the virtual endpoint. -/
theorem choose_lt_limit (query : ℚ) (lower : Nat) (inside : lower < limit)
    (below : query < overflowThreshold) : AdjacentRounding.choose magnitude query lower < limit := by
  by_cases boundary : lower + 1 = limit
  · have previous : lower = limit - 1 := by omega
    have strict : 2 * query < magnitude lower + magnitude (lower + 1) := by
      rw [previous, show limit - 1 + 1 = limit by decide]
      unfold overflowThreshold at below
      linarith
    simp only [AdjacentRounding.choose, strict, ↓reduceIte]
    exact inside
  · rcases AdjacentRounding.choose_endpoints magnitude query lower with left | right
    · rw [left]
      exact inside
    · rw [right]
      omega

/-- Nonoverflow conversion satisfies global nearest-even selection, including
its actual endpoint parity; this is stronger than distance optimality alone. -/
theorem roundIndex_nearestEven (query : ℚ) (nonnegative : 0 ≤ query)
    (below : query < overflowThreshold) :
    roundIndex query < limit ∧ AdjacentRounding.NearestEven magnitude query (roundIndex query) := by
  have notNegative : ¬query < 0 := not_lt_of_ge nonnegative
  have notOverflow : ¬overflowThreshold ≤ query := not_le_of_gt below
  simp only [roundIndex, notNegative, notOverflow, ↓reduceIte]
  obtain ⟨inside, left, right⟩ := bracket_spec query nonnegative below
  exact ⟨choose_lt_limit query _ inside below,
    AdjacentRounding.choose_correct magnitude magnitude_strictMono query _ left right.le⟩

/-- Exactly the specified overflow threshold, including its nearest-even tie,
produces positive infinity. -/
theorem roundIndex_overflow_iff (query : ℚ) (nonnegative : 0 ≤ query) :
    roundIndex query = limit ↔ overflowThreshold ≤ query := by
  constructor
  · intro equal
    by_contra below
    have bounded := (roundIndex_nearestEven query nonnegative (lt_of_not_ge below)).1
    rw [equal] at bounded
    omega
  · intro overflow
    simp [roundIndex, not_lt_of_ge nonnegative, overflow]

theorem roundIndex_le_limit (query : ℚ) : roundIndex query ≤ limit := by
  by_cases negative : query < 0
  · simp [roundIndex, negative]
  · by_cases overflow : overflowThreshold ≤ query
    · simp [roundIndex, negative, overflow]
    · exact (roundIndex_nearestEven query (le_of_not_gt negative) (lt_of_not_ge overflow)).1.le

/-- The checked natural output is represented without unsigned wraparound. -/
theorem roundPositive_toNat (query : ℚ) : (roundPositive query).toNat = roundIndex query := by
  have bound := roundIndex_le_limit query
  simp only [roundPositive]
  apply Nat.mod_eq_of_lt
  unfold limit at bound
  norm_num at bound ⊢
  omega

/-- The bisection converter returns a specified nonzero endpoint when both
neighbor midpoint tests favor it, including even endpoint ties. -/
theorem roundIndex_of_midpoints (query : ℚ) (nonnegative : 0 ≤ query)
    (below : query < overflowThreshold) (index : Nat) (positive : 0 < index)
    (lower : magnitude (index - 1) + magnitude index ≤ 2 * query)
    (upper : 2 * query ≤ magnitude index + magnitude (index + 1))
    (lowerEven : 2 * query = magnitude (index - 1) + magnitude index → index % 2 = 0)
    (upperEven : 2 * query = magnitude index + magnitude (index + 1) → index % 2 = 0) :
    roundIndex query = index := by
  have notNegative : ¬query < 0 := not_lt_of_ge nonnegative
  have notOverflow : ¬overflowThreshold ≤ query := not_le_of_gt below
  simp only [roundIndex, notNegative, notOverflow, ↓reduceIte]
  have initialLeft : magnitude 0 ≤ query := by simpa only [magnitude_zero] using nonnegative
  have initialRight : query < magnitude limit := below.trans overflowThreshold_lt_limit
  by_cases rightHalf : magnitude index ≤ query
  · have gap := magnitude_strictMono (Nat.lt_succ_self index)
    have next : query < magnitude (index + 1) := by linarith
    rw [Bisection.lastLE_eq magnitude magnitude_strictMono query 0 limit (by decide)
      initialLeft initialRight index rightHalf next]
    exact AdjacentRounding.choose_lower magnitude query index upper upperEven
  · have previous : index - 1 + 1 = index := by omega
    have gap := magnitude_strictMono (show index - 1 < index by omega)
    have last : magnitude (index - 1) ≤ query := by linarith
    have next : query < magnitude (index - 1 + 1) := by rw [previous]; exact lt_of_not_ge rightHalf
    rw [Bisection.lastLE_eq magnitude magnitude_strictMono query 0 limit (by decide)
      initialLeft initialRight (index - 1) last next]
    have chosen := AdjacentRounding.choose_upper magnitude query (index - 1)
      (by simpa only [previous] using lower) (by simpa only [previous] using lowerEven)
    simpa only [previous] using chosen

end Silmaril.Numeric.Ieee754.RationalRounding
