module

public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Adjacent magnitudes in binary interchange encodings

The unsigned finite field formula is parameterized by trailing significand
bits and exponent bias. Exact successor spacing includes gradual underflow and
binade transitions, with no enumeration of bit patterns.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.BinaryMagnitude

/-- Width of the trailing significand field as a natural radix. -/
def radix (fractionBits : Nat) : Nat := 2 ^ fractionBits

/-- The subnormal binade shares its spacing with the first normal binade. -/
def spacing (fractionBits : Nat) (bias : Int) (exponent : Nat) : ℚ :=
  (2 : ℚ) ^ ((max exponent 1 : Nat) - bias - fractionBits : Int)

def significand (fractionBits exponent fraction : Nat) : Nat :=
  if exponent = 0 then fraction else radix fractionBits + fraction

/-- The positive finite value formula, extended arithmetically to all natural
encodings. An IEEE caller separately excludes sign and exceptional fields. -/
def value (fractionBits : Nat) (bias : Int) (encoding : Nat) : ℚ :=
  (significand fractionBits (encoding / radix fractionBits) (encoding % radix fractionBits) : ℚ) *
    spacing fractionBits bias (encoding / radix fractionBits)

theorem radix_pos (fractionBits : Nat) : 0 < radix fractionBits := Nat.two_pow_pos _

theorem spacing_pos (fractionBits : Nat) (bias : Int) (exponent : Nat) :
    0 < spacing fractionBits bias exponent := zpow_pos (by norm_num) _

@[simp] theorem spacing_zero (fractionBits : Nat) (bias : Int) :
    spacing fractionBits bias 0 = spacing fractionBits bias 1 := by simp [spacing]

theorem spacing_succ (fractionBits : Nat) (bias : Int) (exponent : Nat)
    (positive : 0 < exponent) :
    spacing fractionBits bias (exponent + 1) = 2 * spacing fractionBits bias exponent := by
  have h : 1 ≤ exponent := positive
  simp only [spacing, max_eq_left h, max_eq_left (by omega : 1 ≤ exponent + 1), Nat.cast_add, Nat.cast_one]
  have power : (exponent : Int) + 1 - bias - fractionBits =
      ((exponent : Int) - bias - fractionBits) + 1 := by omega
  rw [power, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp only [zpow_one, mul_comm]

/-- Division and remainder of a successor split into within-field increment
and field rollover. This arithmetic lemma works for every positive radix. -/
theorem successor_fields (encoding base : Nat) (positive : 0 < base) :
    (encoding % base + 1 < base ∧
      (encoding + 1) / base = encoding / base ∧
      (encoding + 1) % base = encoding % base + 1) ∨
    (encoding % base + 1 = base ∧
      (encoding + 1) / base = encoding / base + 1 ∧
      (encoding + 1) % base = 0) := by
  have remainder := Nat.mod_lt encoding positive
  have decomposition : encoding + 1 = (encoding % base + 1) + base * (encoding / base) := by
    have divided := Nat.mod_add_div encoding base
    omega
  by_cases inside : encoding % base + 1 < base
  · refine Or.inl ⟨inside, ?_, ?_⟩
    · rw [decomposition, Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt inside, Nat.zero_add]
    · rw [decomposition, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt inside]
  · have carry : encoding % base + 1 = base := by omega
    refine Or.inr ⟨carry, ?_, ?_⟩
    · rw [decomposition, carry, Nat.add_mul_div_left _ _ positive, Nat.div_self positive, Nat.add_comm]
    · rw [decomposition, carry, Nat.add_mul_mod_self_left, Nat.mod_self]

/-- The gap to the next encoding is exactly the current binade's spacing. -/
theorem value_succ (fractionBits : Nat) (bias : Int) (encoding : Nat) :
    value fractionBits bias (encoding + 1) =
      value fractionBits bias encoding + spacing fractionBits bias (encoding / radix fractionBits) := by
  rcases successor_fields encoding (radix fractionBits) (radix_pos fractionBits) with
    ⟨_, quotient, remainder⟩ | ⟨carry, quotient, remainder⟩
  · simp only [value, quotient, remainder, significand]
    split <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring
  · have castCarry : (encoding % radix fractionBits : ℚ) + 1 = radix fractionBits := by
      exact_mod_cast carry
    simp only [value, quotient, remainder, significand, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte, Nat.add_zero]
    by_cases subnormal : encoding / radix fractionBits = 0
    · simp only [subnormal, ↓reduceIte, Nat.zero_add, spacing_zero]
      rw [← castCarry]
      ring
    · simp only [subnormal, ↓reduceIte, Nat.cast_add]
      rw [spacing_succ fractionBits bias _ (Nat.pos_of_ne_zero subnormal), ← castCarry]
      ring

theorem significand_bound (fractionBits encoding : Nat) :
    significand fractionBits (encoding / radix fractionBits) (encoding % radix fractionBits) + 1 ≤
      2 * radix fractionBits := by
  have remainder := Nat.mod_lt encoding (radix_pos fractionBits)
  have positive := radix_pos fractionBits
  unfold significand
  split <;> omega

theorem value_nonneg (fractionBits : Nat) (bias : Int) (encoding : Nat) :
    0 ≤ value fractionBits bias encoding :=
  mul_nonneg (Nat.cast_nonneg _) (spacing_pos fractionBits bias _).le

theorem value_pos (fractionBits : Nat) (bias : Int) (encoding : Nat) (positive : 0 < encoding) :
    0 < value fractionBits bias encoding := by
  apply mul_pos _ (spacing_pos fractionBits bias _)
  apply Nat.cast_pos.mpr
  unfold significand
  split
  next subnormal =>
    have reconstruction := Nat.mod_add_div encoding (radix fractionBits)
    simp only [subnormal, Nat.mul_zero, Nat.add_zero] at reconstruction
    omega
  next normal => have base := radix_pos fractionBits; omega

/-- Both endpoints of an adjacent pair fit within `2^(fractionBits+1)`
current spacings. The upper endpoint is tight at a normal binade boundary. -/
theorem endpoints_bound (fractionBits : Nat) (bias : Int) (encoding : Nat) :
    value fractionBits bias encoding ≤
        (2 * radix fractionBits : Nat) * spacing fractionBits bias (encoding / radix fractionBits) ∧
      value fractionBits bias (encoding + 1) ≤
        (2 * radix fractionBits : Nat) * spacing fractionBits bias (encoding / radix fractionBits) := by
  have bound : (significand fractionBits (encoding / radix fractionBits)
      (encoding % radix fractionBits) : ℚ) + 1 ≤ (2 * radix fractionBits : Nat) := by
    exact_mod_cast significand_bound fractionBits encoding
  have spacingPositive := spacing_pos fractionBits bias (encoding / radix fractionBits)
  have upper := mul_le_mul_of_nonneg_right bound spacingPositive.le
  constructor
  · unfold value
    nlinarith
  · rw [value_succ]
    simpa only [value, add_mul, one_mul] using upper

/-- The normalized significand formula agrees with the usual IEEE field
formula, including zero and subnormal encodings. -/
theorem value_field_formula (fractionBits : Nat) (bias : Int) (encoding : Nat) :
    value fractionBits bias encoding =
      if encoding / radix fractionBits = 0 then
        ((encoding % radix fractionBits : ℚ) / radix fractionBits) * (2 : ℚ) ^ (1 - bias)
      else
        (1 + (encoding % radix fractionBits : ℚ) / radix fractionBits) *
          (2 : ℚ) ^ ((encoding / radix fractionBits : Nat) - bias : Int) := by
  unfold value significand spacing
  by_cases zero : encoding / radix fractionBits = 0
  · simp only [zero, ↓reduceIte, max_eq_right (by omega : 0 ≤ 1), Nat.cast_one]
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
    simp only [radix, Nat.cast_pow, Nat.cast_ofNat, zpow_natCast]
    ring
  · have positive : 1 ≤ encoding / radix fractionBits := Nat.one_le_iff_ne_zero.mpr zero
    simp only [zero, ↓reduceIte, max_eq_left positive, Nat.cast_add]
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
    simp only [radix, Nat.cast_pow, Nat.cast_ofNat, zpow_natCast]
    have nonzero : (2 : ℚ) ^ fractionBits ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [nonzero]

theorem relative_gap (fractionBits : Nat) (bias : Int) (encoding : Nat) :
    value fractionBits bias encoding / (2 * radix fractionBits : Nat) ≤
        value fractionBits bias (encoding + 1) - value fractionBits bias encoding ∧
      value fractionBits bias (encoding + 1) / (2 * radix fractionBits : Nat) ≤
        value fractionBits bias (encoding + 1) - value fractionBits bias encoding := by
  have positive : (0 : ℚ) < (2 * radix fractionBits : Nat) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) (radix_pos fractionBits)
  have gap : value fractionBits bias (encoding + 1) - value fractionBits bias encoding =
      spacing fractionBits bias (encoding / radix fractionBits) := by rw [value_succ]; ring
  rw [gap]
  obtain ⟨left, right⟩ := endpoints_bound fractionBits bias encoding
  constructor
  · exact (div_le_iff₀ positive).mpr (by simpa only [mul_comm] using left)
  · exact (div_le_iff₀ positive).mpr (by simpa only [mul_comm] using right)

end Silmaril.Numeric.Ieee754.BinaryMagnitude
