module

public import Silmaril.Numeric.Ieee754.Std.Ops

/-!
# Integer rounding is grid rounding

`roundIntMag`, the integer rounding used by roundToIntegral, remainder and
float-to-integer conversion (`Std.Ops`), picks between the floor and the ceiling
of the magnitude. `roundIntMag_eq_roundMagQ` proves that it is the rounding onto
the integer grid `intGrid p` (precision `p + 1`, least quantum exponent `0`) for
any `p` with `x < 2^p`, so `roundIntMag_spec` gives it the order-theoretic
specification `Grid.RoundMag` of `Std.Round` (greatest representable integer
below, least above, direction and ties as for every other rounding), and
`roundIntMag_unique` shows that the specification determines it.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-- Integers below `2^(p+1)`, as a grid. -/
def intGrid (p : ℕ) : Grid := ⟨p + 1, some 0⟩

theorem roundIntMag_eq_roundMagQ (mode : RoundingMode) (neg : Bool) {x : ℚ} (hx : 0 ≤ x)
    {p : ℕ} (hp : x < 2 ^ p) :
    (roundIntMag mode neg x : ℚ) = (intGrid p).roundMagQ mode neg x := by
  rcases hx.lt_or_eq with hx | rfl
  · have hq : (intGrid p).qexpQ x = 0 := by
      rw [Grid.qexpQ_eq _ hx]
      have hlog : Int.log 2 x < p := by
        have := (Int.lt_zpow_iff_log_lt (R := ℚ) (b := 2) (x := (p : ℤ)) (by norm_num) hx).mp
          (by rw [zpow_natCast]; exact_mod_cast hp)
        exact this
      simp only [Grid.qexp, Grid.clamp, intGrid]
      push_cast
      omega
    simp only [Grid.roundMagQ, hq, zpow_zero, div_one, mul_one]
    unfold roundIntMag
    rcases pickBy_cases mode neg (x - ⌊x⌋₊ < ⌈x⌉₊ - x) (⌈x⌉₊ - x < x - ⌊x⌋₊) (⌊x⌋₊ % 2 = 0)
      (⌊x⌋₊ : ℚ) (⌈x⌉₊ : ℚ) with h | h
    · have h' : pick mode neg (⌊x⌋₊ % 2 = 0) x (⌊x⌋₊ : ℚ) (⌈x⌉₊ : ℚ) = ⌊x⌋₊ := h
      simp only [h', ite_true]
    · have h' : pick mode neg (⌊x⌋₊ % 2 = 0) x (⌊x⌋₊ : ℚ) (⌈x⌉₊ : ℚ) = ⌈x⌉₊ := h
      split_ifs with hf
      · rw [hf]
      · rw [h']
  · simp [roundIntMag, Grid.roundMagQ, pick_self]

/-- Integer rounding meets the order-theoretic rounding specification. -/
theorem roundIntMag_spec (mode : RoundingMode) (neg : Bool) {x : ℚ} (hx : 0 ≤ x) {p : ℕ}
    (hp : x < 2 ^ p) : (intGrid p).RoundMag mode neg x (roundIntMag mode neg x : ℚ) := by
  rw [roundIntMag_eq_roundMagQ mode neg hx hp]
  exact (intGrid p).roundMagQ_spec (by simp [intGrid]) mode neg hx

/-- The specification determines integer rounding. -/
theorem roundIntMag_unique (mode : RoundingMode) (neg : Bool) {x : ℚ} (hx : 0 ≤ x) {p : ℕ}
    (hp : x < 2 ^ p) {r : ℚ} (h : (intGrid p).RoundMag mode neg x r) :
    r = roundIntMag mode neg x :=
  h.unique (roundIntMag_spec mode neg hx hp)

end Silmaril.Numeric.Ieee754.Std
