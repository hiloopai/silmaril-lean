module

public import Silmaril.Numeric.Ieee754
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Directed integer rounding and rounding on a binary grid

This module is the arithmetic core of the exception-flag specification. It is
stated over any linearly ordered field with a floor function, so the same
definitions are computable over `ℚ` and describe irrational exact results over
`ℝ`. Nothing here depends on the executable rounding in
`Numeric.Ieee754.Rounding`.

`roundInt mode x` is the integer selected from `x` by one of the five rounding
directions of IEEE 754-2019 §4.3: `towardNegative` is the floor,
`towardPositive` the ceiling, `towardZero` truncation, and the two nearest
directions choose the nearer of floor and ceiling, resolving a midpoint to the
even integer (§4.3.1) or away from zero (§4.3.1). `roundAt mode q x` rounds `x`
to an integer multiple of `2 ^ q`.

The theorems establish the properties later used for exception classification:
integers are fixed, rounding is monotone, a value is fixed exactly when it is a
multiple of the grid spacing, and rational inputs round identically in every
larger ordered field.

Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

universe u

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- The integer selected from `x` by an IEEE rounding direction (§4.3). -/
def roundInt (mode : RoundingMode) (x : K) : ℤ :=
  match mode with
  | .towardNegative => ⌊x⌋
  | .towardPositive => ⌈x⌉
  | .towardZero => if 0 ≤ x then ⌊x⌋ else ⌈x⌉
  | .nearestTiesToEven =>
    if Int.fract x < 1 / 2 then ⌊x⌋
    else if 1 / 2 < Int.fract x then ⌊x⌋ + 1
    else if ⌊x⌋ % 2 = 0 then ⌊x⌋ else ⌊x⌋ + 1
  | .nearestTiesToAway =>
    if Int.fract x < 1 / 2 then ⌊x⌋
    else if 1 / 2 < Int.fract x then ⌊x⌋ + 1
    else if 0 ≤ x then ⌊x⌋ + 1 else ⌊x⌋

/-- Round `x` to an integer multiple of `2 ^ q` in the given direction. -/
def roundAt (mode : RoundingMode) (q : ℤ) (x : K) : K :=
  (roundInt mode (x / 2 ^ q) : K) * 2 ^ q

omit [FloorRing K] in
theorem two_zpow_pos (q : ℤ) : (0 : K) < 2 ^ q := zpow_pos (by norm_num) q

omit [FloorRing K] in
theorem two_zpow_ne_zero (q : ℤ) : (2 : K) ^ q ≠ 0 := (two_zpow_pos q).ne'

/-- Integers are unchanged in every direction. -/
@[simp] theorem roundInt_intCast (mode : RoundingMode) (n : ℤ) : roundInt mode (n : K) = n := by
  cases mode <;> simp [roundInt, Int.fract_intCast]

@[simp] theorem roundInt_zero (mode : RoundingMode) : roundInt mode (0 : K) = 0 := by
  simpa using roundInt_intCast (K := K) mode 0

/-- Every direction selects the floor or the next integer. -/
theorem floor_le_roundInt (mode : RoundingMode) (x : K) : ⌊x⌋ ≤ roundInt mode x := by
  cases mode <;> simp only [roundInt]
  · split_ifs <;> omega
  · split_ifs
    · exact le_rfl
    · exact Int.floor_le_ceil x
  · exact Int.floor_le_ceil x
  · exact le_rfl
  · split_ifs <;> omega

omit [IsStrictOrderedRing K] in
theorem roundInt_le_floor_add_one (mode : RoundingMode) (x : K) : roundInt mode x ≤ ⌊x⌋ + 1 := by
  cases mode <;> simp only [roundInt]
  · split_ifs <;> omega
  · split_ifs
    · omega
    · exact Int.ceil_le_floor_add_one x
  · exact Int.ceil_le_floor_add_one x
  · omega
  · split_ifs <;> omega

omit [IsStrictOrderedRing K] in
/-- The nearest directions round down strictly below a midpoint. -/
theorem roundInt_nearest_of_fract_lt {mode : RoundingMode}
    (hmode : mode = .nearestTiesToEven ∨ mode = .nearestTiesToAway) {x : K}
    (h : Int.fract x < 1 / 2) : roundInt mode x = ⌊x⌋ := by
  rcases hmode with rfl | rfl <;> simp only [roundInt, h, ↓reduceIte]

omit [IsStrictOrderedRing K] in
/-- The nearest directions round up strictly above a midpoint. -/
theorem roundInt_nearest_of_lt_fract {mode : RoundingMode}
    (hmode : mode = .nearestTiesToEven ∨ mode = .nearestTiesToAway) {x : K}
    (h : 1 / 2 < Int.fract x) : roundInt mode x = ⌊x⌋ + 1 := by
  have h' : ¬ Int.fract x < 1 / 2 := not_lt.mpr h.le
  rcases hmode with rfl | rfl <;> simp only [roundInt, h, h', ↓reduceIte]

/-- Every IEEE rounding direction is monotone. -/
theorem roundInt_mono (mode : RoundingMode) {x y : K} (hxy : x ≤ y) :
    roundInt mode x ≤ roundInt mode y := by
  have hfloor : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_le_floor hxy
  -- The nearest directions: compare fractional parts when the floors agree.
  have nearest : ∀ m : RoundingMode, (m = .nearestTiesToEven ∨ m = .nearestTiesToAway) →
      roundInt m x ≤ roundInt m y := by
    intro m hm
    rcases lt_or_eq_of_le hfloor with hlt | heq
    · have h1 := roundInt_le_floor_add_one m x
      have h2 := floor_le_roundInt m y
      omega
    · have hx := Int.floor_add_fract x
      have hy := Int.floor_add_fract y
      have hfr : Int.fract x ≤ Int.fract y := by
        rw [heq] at hx
        linarith
      rcases lt_trichotomy (Int.fract x) (1 / 2) with hxl | hxe | hxg
      · rw [roundInt_nearest_of_fract_lt hm hxl, heq]
        exact floor_le_roundInt m y
      · rcases lt_or_eq_of_le hfr with hlt | hfe
        · rw [roundInt_nearest_of_lt_fract hm (show 1 / 2 < Int.fract y by rw [← hxe]; exact hlt),
            ← heq]
          exact roundInt_le_floor_add_one m x
        · have : x = y := by
            rw [heq] at hx
            linarith
          rw [this]
      · rw [roundInt_nearest_of_lt_fract hm hxg,
          roundInt_nearest_of_lt_fract hm (lt_of_lt_of_le hxg hfr), heq]
  cases mode
  · exact nearest _ (Or.inl rfl)
  · simp only [roundInt]
    split_ifs with hx hy hy
    · exact hfloor
    · exact absurd (le_trans hx hxy) hy
    · have : ⌈x⌉ ≤ 0 := Int.ceil_le.mpr (by push_cast; linarith [not_le.mp hx])
      have : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy
      omega
    · exact Int.ceil_le_ceil hxy
  · exact Int.ceil_le_ceil hxy
  · exact hfloor
  · exact nearest _ (Or.inr rfl)

/-- A value is unchanged by integer rounding exactly when it is an integer. -/
theorem roundInt_eq_self_iff (mode : RoundingMode) (x : K) :
    ((roundInt mode x : ℤ) : K) = x ↔ ∃ n : ℤ, (n : K) = x := by
  constructor
  · intro h
    exact ⟨_, h⟩
  · rintro ⟨n, rfl⟩
    simp

/-- Rounding a rational in a larger ordered field selects the same integer. -/
theorem roundInt_ratCast {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    [FloorRing L] (mode : RoundingMode) (x : ℚ) : roundInt mode (x : L) = roundInt mode x := by
  have hfract : Int.fract (x : L) = ((Int.fract x : ℚ) : L) := by
    unfold Int.fract
    rw [Rat.floor_cast]
    push_cast
    ring
  have hlt : Int.fract (x : L) < 1 / 2 ↔ Int.fract x < 1 / 2 := by
    rw [hfract, show (1 / 2 : L) = ((1 / 2 : ℚ) : L) by push_cast; ring, Rat.cast_lt]
  have hgt : 1 / 2 < Int.fract (x : L) ↔ 1 / 2 < Int.fract x := by
    rw [hfract, show (1 / 2 : L) = ((1 / 2 : ℚ) : L) by push_cast; ring, Rat.cast_lt]
  have hnonneg : (0 : L) ≤ x ↔ 0 ≤ x := Rat.cast_nonneg
  cases mode <;> simp only [roundInt, Rat.floor_cast, Rat.ceil_cast, hlt, hgt, hnonneg]

/-! ## Rounding on the grid `2 ^ q · ℤ` -/

@[simp] theorem roundAt_zero (mode : RoundingMode) (q : ℤ) : roundAt mode q (0 : K) = 0 := by
  simp [roundAt]

/-- Grid points are unchanged. -/
@[simp] theorem roundAt_intMul (mode : RoundingMode) (q n : ℤ) :
    roundAt mode q ((n : K) * 2 ^ q) = n * 2 ^ q := by
  simp [roundAt, mul_div_assoc, div_self (two_zpow_ne_zero (K := K) q)]

theorem roundAt_mono (mode : RoundingMode) (q : ℤ) {x y : K} (hxy : x ≤ y) :
    roundAt mode q x ≤ roundAt mode q y := by
  unfold roundAt
  have hq := two_zpow_pos (K := K) q
  have hdiv : x / 2 ^ q ≤ y / 2 ^ q := div_le_div_of_nonneg_right hxy hq.le
  have := roundInt_mono mode hdiv
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hq.le

/-- Grid rounding fixes `x` exactly when `x` is an integer multiple of `2 ^ q`. -/
theorem roundAt_eq_self_iff (mode : RoundingMode) (q : ℤ) (x : K) :
    roundAt mode q x = x ↔ ∃ n : ℤ, x = n * 2 ^ q := by
  constructor
  · intro h
    exact ⟨roundInt mode (x / 2 ^ q), h.symm⟩
  · rintro ⟨n, rfl⟩
    exact roundAt_intMul mode q n

omit [FloorRing K] in
/-- A multiple of a coarser grid spacing is a multiple of every finer one. -/
theorem intMul_of_le {q q' : ℤ} (hq : q ≤ q') (n : ℤ) :
    ∃ m : ℤ, (n : K) * 2 ^ q' = m * 2 ^ q := by
  refine ⟨n * 2 ^ (q' - q).toNat, ?_⟩
  have hsplit : (2 : K) ^ q' = 2 ^ (q' - q) * 2 ^ q := by
    rw [← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
    congr 1
    ring
  have hnat : (2 : K) ^ (q' - q) = ((2 ^ (q' - q).toNat : ℤ) : K) := by
    rw [Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hq)]
  rw [hsplit, hnat]
  push_cast
  ring

/-- Grid rounding does not reduce a magnitude below a power of two on a coarser
grid. This is the monotonicity fact behind the comparison of tininess rules. -/
theorem le_abs_roundAt (mode : RoundingMode) {q k : ℤ} (hqk : q ≤ k) {x : K}
    (hx : (2 : K) ^ k ≤ |x|) : (2 : K) ^ k ≤ |roundAt mode q x| := by
  obtain ⟨m, hm⟩ := intMul_of_le (K := K) hqk 1
  simp only [Int.cast_one, one_mul] at hm
  have hfix : roundAt mode q ((2 : K) ^ k) = 2 ^ k := by
    rw [hm]
    exact roundAt_intMul mode q m
  have hfixNeg : roundAt mode q (-(2 : K) ^ k) = -2 ^ k := by
    rw [hm, ← neg_mul, ← Int.cast_neg]
    rw [roundAt_intMul]
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    have := roundAt_mono mode q hx
    rw [hfix] at this
    exact le_trans this (le_abs_self _)
  · rw [abs_of_neg h0] at hx
    have := roundAt_mono mode q (show x ≤ -(2 : K) ^ k by linarith)
    rw [hfixNeg] at this
    rw [abs_of_nonpos (by linarith [two_zpow_pos (K := K) k])]
    linarith

/-- Grid rounding does not increase a magnitude above a grid point. -/
theorem abs_roundAt_le (mode : RoundingMode) (q : ℤ) {x : K} (bound : ℤ)
    (hx : |x| ≤ (bound : K) * 2 ^ q) : |roundAt mode q x| ≤ (bound : K) * 2 ^ q := by
  have hup := roundAt_mono mode q (le_trans (le_abs_self x) hx)
  have hlo := roundAt_mono mode q (show -((bound : K) * 2 ^ q) ≤ x by
    linarith [neg_abs_le x])
  rw [roundAt_intMul] at hup
  rw [← neg_mul, ← Int.cast_neg, roundAt_intMul] at hlo
  push_cast at hlo
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- A nonnegative input rounds to a nonnegative grid point. -/
theorem roundAt_nonneg (mode : RoundingMode) (q : ℤ) {x : K} (hx : 0 ≤ x) :
    0 ≤ roundAt mode q x := by
  have := roundAt_mono mode q hx
  rwa [roundAt_zero] at this

theorem roundAt_ratCast {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    [FloorRing L] (mode : RoundingMode) (q : ℤ) (x : ℚ) :
    roundAt mode q (x : L) = ((roundAt mode q x : ℚ) : L) := by
  unfold roundAt
  have : (x : L) / 2 ^ q = ((x / 2 ^ q : ℚ) : L) := by push_cast; rfl
  rw [this, roundInt_ratCast]
  push_cast
  rfl

end Silmaril.Numeric.Ieee754.FlagSpec
