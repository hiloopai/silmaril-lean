module

public import Silmaril.Numeric.Ieee754.Flags.Rounding
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exceptions raised by rounding a square root

The exact result of `squareRoot(a)` (IEEE 754-2019 §5.4.1) is usually
irrational, so its exceptions are specified by `roundingFlags` over `ℝ`, applied
to `Real.sqrt a`. That classification is not computable. This module gives a
computable classification from rational comparisons alone, and proves that it
equals the real one for every nonnegative rational `a`
(`sqrtRoundingFlags_eq`).

The computation uses two facts: `⌊√s⌋ = Nat.sqrt ⌊s⌋₊` for `0 ≤ s`, and for
`0 ≤ c`, `√s < c ↔ s < c ^ 2`. Midpoints and exactness of `√a` are decided by
comparing `a` with squares of rationals, so no approximation of `√a` is used.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model

/-- The integer selected from `√s` by a rounding direction, for `0 ≤ s`, using
rational comparisons only. -/
def roundIntSqrt (mode : RoundingMode) (s : ℚ) : ℤ :=
  let n : ℤ := (Nat.sqrt ⌊s⌋₊ : ℤ)
  match mode with
  | .towardNegative | .towardZero => n
  | .towardPositive => if (n : ℚ) * n = s then n else n + 1
  | .nearestTiesToEven =>
    if s < ((n : ℚ) + 1 / 2) ^ 2 then n
    else if ((n : ℚ) + 1 / 2) ^ 2 < s then n + 1
    else if n % 2 = 0 then n else n + 1
  | .nearestTiesToAway => if s < ((n : ℚ) + 1 / 2) ^ 2 then n else n + 1

/-- `⌊√s⌋` for a nonnegative rational, via the integer square root of `⌊s⌋₊`. -/
theorem floor_sqrt_ratCast {s : ℚ} (hs : 0 ≤ s) :
    ⌊Real.sqrt (s : ℝ)⌋ = (Nat.sqrt ⌊s⌋₊ : ℤ) := by
  set n : ℕ := Nat.sqrt ⌊s⌋₊ with hn
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [Real.le_sqrt (by positivity) hsR]
    have h1 : n ^ 2 ≤ ⌊s⌋₊ := Nat.sqrt_le' _
    have h2 : ((⌊s⌋₊ : ℕ) : ℚ) ≤ s := Nat.floor_le hs
    have h3 : ((n ^ 2 : ℕ) : ℚ) ≤ s := le_trans (by exact_mod_cast h1) h2
    exact_mod_cast h3
  · rw [Real.sqrt_lt' (by positivity)]
    have h1 : ⌊s⌋₊ < (n + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have h2 : s < (((n + 1) ^ 2 : ℕ) : ℚ) := (Nat.floor_lt hs).mp h1
    exact_mod_cast h2

/-- The rational comparisons of `roundIntSqrt` select the same integer as
rounding the real square root. -/
theorem roundIntSqrt_eq (mode : RoundingMode) {s : ℚ} (hs : 0 ≤ s) :
    roundIntSqrt mode s = roundInt mode (Real.sqrt (s : ℝ)) := by
  set r := Real.sqrt (s : ℝ) with hr
  set n : ℤ := (Nat.sqrt ⌊s⌋₊ : ℤ) with hn
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hfl : ⌊r⌋ = n := floor_sqrt_ratCast hs
  have hn0 : (0 : ℝ) ≤ n := by rw [hn]; positivity
  have hfract : Int.fract r = r - n := by rw [← Int.self_sub_floor, hfl]
  have key : ((n : ℝ) + 1 / 2) ^ 2 = ((((n : ℚ) + 1 / 2) ^ 2 : ℚ) : ℝ) := by push_cast; ring
  have hA : Int.fract r < 1 / 2 ↔ s < ((n : ℚ) + 1 / 2) ^ 2 := by
    rw [hfract, show r - n < 1 / 2 ↔ r < (n : ℝ) + 1 / 2 by constructor <;> intro h <;> linarith,
      hr, Real.sqrt_lt' (by positivity), key, Rat.cast_lt]
  have hB : 1 / 2 < Int.fract r ↔ ((n : ℚ) + 1 / 2) ^ 2 < s := by
    rw [hfract, show 1 / 2 < r - n ↔ (n : ℝ) + 1 / 2 < r by constructor <;> intro h <;> linarith,
      hr, Real.lt_sqrt (by positivity), key, Rat.cast_lt]
  have hC : ⌈r⌉ = if (n : ℚ) * n = s then n else n + 1 := by
    split
    · next h =>
      have : r = n := by
        rw [hr, ← Real.sqrt_mul_self hn0]
        congr 1
        exact_mod_cast h.symm
      rw [this, Int.ceil_intCast]
    · next h =>
      have hne : r ≠ n := by
        intro heq
        apply h
        have : (s : ℝ) = n * n := (Real.sqrt_eq_iff_mul_self_eq hsR hn0).mp heq
        exact_mod_cast this.symm
      have hlo : (n : ℝ) ≤ r := by rw [← hfl]; exact Int.floor_le r
      have hhi : r < (n : ℝ) + 1 := by rw [← hfl]; exact Int.lt_floor_add_one r
      rw [Int.ceil_eq_iff]
      push_cast
      constructor
      · exact lt_of_le_of_ne (by linarith) (Ne.symm (by simpa using hne))
      · linarith
  cases mode <;> simp only [roundIntSqrt, roundInt, ← hn, hfl, hA, hB, hC, hr0, ↓reduceIte]
  split_ifs <;> rfl

/-- Round `√a` to the grid `2 ^ q · ℤ`, from rational comparisons. -/
def sqrtRoundAt (mode : RoundingMode) (q : ℤ) (a : ℚ) : ℚ :=
  (roundIntSqrt mode (a / 2 ^ (2 * q)) : ℚ) * 2 ^ q

theorem roundAt_sqrt (mode : RoundingMode) (q : ℤ) {a : ℚ} (ha : 0 ≤ a) :
    roundAt mode q (Real.sqrt (a : ℝ)) = ((sqrtRoundAt mode q a : ℚ) : ℝ) := by
  have hdiv : Real.sqrt (a : ℝ) / 2 ^ q = Real.sqrt (((a / 2 ^ (2 * q) : ℚ) : ℝ)) := by
    have hpos : (0 : ℝ) ≤ 2 ^ q := (two_zpow_pos q).le
    have hsq : (2 : ℝ) ^ (2 * q) = (2 ^ q) ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    push_cast
    rw [Real.sqrt_div' _ (by positivity), hsq, Real.sqrt_sq hpos]
  have hs : 0 ≤ a / 2 ^ (2 * q) := div_nonneg ha (two_zpow_pos _).le
  unfold roundAt sqrtRoundAt
  rw [hdiv, ← roundIntSqrt_eq mode hs]
  push_cast
  rfl

/-- The leading exponent of `√a`, computed from that of `a`. -/
def sqrtLeadingExponent (a : ℚ) : ℤ := leadingExponent a / 2

theorem leadingExponent_sqrt {a : ℚ} (ha : 0 ≤ a) :
    leadingExponent (Real.sqrt (a : ℝ)) = sqrtLeadingExponent a := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · subst h0
    simp [leadingExponent, sqrtLeadingExponent]
  set L := leadingExponent a with hL
  set e := L / 2 with he
  have haR : (0 : ℝ) < a := by exact_mod_cast hpos
  have hlo : (2 : ℚ) ^ L ≤ a := by
    have := two_zpow_leadingExponent_le hpos.ne'
    rwa [abs_of_pos hpos] at this
  have hhi : a < (2 : ℚ) ^ (L + 1) := by
    have := abs_lt_two_zpow_leadingExponent a
    rwa [abs_of_pos hpos] at this
  have he1 : e * 2 ≤ L := Int.ediv_mul_le L (by norm_num)
  have he2 : L < (e + 1) * 2 := Int.lt_ediv_add_one_mul_self L (by norm_num)
  unfold sqrtLeadingExponent
  rw [← hL, ← he]
  apply leadingExponent_eq
  · rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.le_sqrt (two_zpow_pos e).le haR.le,
      ← zpow_natCast, ← zpow_mul]
    have : (2 : ℚ) ^ (e * ((2 : ℕ) : ℤ)) ≤ a :=
      le_trans (zpow_le_zpow_right₀ (by norm_num) (by simpa using he1)) hlo
    have hc : (((2 : ℚ) ^ (e * ((2 : ℕ) : ℤ)) : ℚ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast this
    rwa [two_zpow_ratCast] at hc
  · rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_lt' (two_zpow_pos _),
      ← zpow_natCast, ← zpow_mul]
    have : a < (2 : ℚ) ^ ((e + 1) * ((2 : ℕ) : ℤ)) :=
      lt_of_lt_of_le hhi (zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega))
    have hc : (a : ℝ) < (((2 : ℚ) ^ ((e + 1) * ((2 : ℕ) : ℤ)) : ℚ) : ℝ) := by exact_mod_cast this
    rwa [two_zpow_ratCast] at hc

/-- `roundUnbounded` of `√a`, from rational comparisons. -/
def sqrtRoundUnbounded (f : Format) (mode : RoundingMode) (a : ℚ) : ℚ :=
  sqrtRoundAt mode (sqrtLeadingExponent a - (precision f - 1)) a

/-- `roundGradual` of `√a`, from rational comparisons. -/
def sqrtRoundGradual (f : Format) (mode : RoundingMode) (a : ℚ) : ℚ :=
  sqrtRoundAt mode (max (sqrtLeadingExponent a) (emin f) - (precision f - 1)) a

theorem roundUnbounded_sqrt (f : Format) (mode : RoundingMode) {a : ℚ} (ha : 0 ≤ a) :
    roundUnbounded f mode (Real.sqrt (a : ℝ)) = ((sqrtRoundUnbounded f mode a : ℚ) : ℝ) := by
  unfold roundUnbounded unboundedQuantum sqrtRoundUnbounded
  rw [leadingExponent_sqrt ha, roundAt_sqrt mode _ ha]

theorem roundGradual_sqrt (f : Format) (mode : RoundingMode) {a : ℚ} (ha : 0 ≤ a) :
    roundGradual f mode (Real.sqrt (a : ℝ)) = ((sqrtRoundGradual f mode a : ℚ) : ℝ) := by
  unfold roundGradual quantum sqrtRoundGradual
  rw [leadingExponent_sqrt ha, roundAt_sqrt mode _ ha]

theorem sqrtRoundUnbounded_nonneg (f : Format) (mode : RoundingMode) {a : ℚ} (ha : 0 ≤ a) :
    0 ≤ sqrtRoundUnbounded f mode a := by
  have h := roundAt_nonneg mode (unboundedQuantum f (Real.sqrt (a : ℝ))) (Real.sqrt_nonneg (a : ℝ))
  change 0 ≤ roundUnbounded f mode _ at h
  rw [roundUnbounded_sqrt f mode ha] at h
  exact_mod_cast h

theorem sqrtRoundGradual_nonneg (f : Format) (mode : RoundingMode) {a : ℚ} (ha : 0 ≤ a) :
    0 ≤ sqrtRoundGradual f mode a := by
  have h := roundAt_nonneg mode (quantum f (Real.sqrt (a : ℝ))) (Real.sqrt_nonneg (a : ℝ))
  change 0 ≤ roundGradual f mode _ at h
  rw [roundGradual_sqrt f mode ha] at h
  exact_mod_cast h

/-- Overflow of `√a`, decided in `ℚ`. -/
def SqrtOverflows (f : Format) (mode : RoundingMode) (a : ℚ) : Prop :=
  maxFinite f < sqrtRoundUnbounded f mode a

/-- Inexactness of `√a`, decided in `ℚ`: overflow, or a finite rounded value
whose square is not `a`. -/
def SqrtInexact (f : Format) (mode : RoundingMode) (a : ℚ) : Prop :=
  SqrtOverflows f mode a ∨ sqrtRoundGradual f mode a * sqrtRoundGradual f mode a ≠ a

/-- Tininess of `√a`, decided in `ℚ`. Before rounding, `√a < 2 ^ emin` is
`a < 2 ^ (2 · emin)`. -/
def SqrtTiny (f : Format) (tininess : Tininess) (mode : RoundingMode) (a : ℚ) : Prop :=
  a ≠ 0 ∧ match tininess with
    | .beforeRounding => a < 2 ^ (2 * emin f)
    | .afterRounding => sqrtRoundUnbounded f mode a < 2 ^ emin f

instance (f : Format) (mode : RoundingMode) (a : ℚ) : Decidable (SqrtOverflows f mode a) :=
  inferInstanceAs (Decidable (_ < _))

instance (f : Format) (mode : RoundingMode) (a : ℚ) : Decidable (SqrtInexact f mode a) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (f : Format) (tininess : Tininess) (mode : RoundingMode) (a : ℚ) :
    Decidable (SqrtTiny f tininess mode a) :=
  match tininess with
  | .beforeRounding => inferInstanceAs (Decidable (_ ∧ _))
  | .afterRounding => inferInstanceAs (Decidable (_ ∧ _))

/-- Computable overflow, underflow and inexact flags for `squareRoot(a)`,
`0 ≤ a`. -/
def sqrtRoundingFlags (f : Format) (mode : RoundingMode) (tininess : Tininess) (a : ℚ) : Flags where
  overflow := decide (SqrtOverflows f mode a)
  underflow := decide (SqrtTiny f tininess mode a ∧ SqrtInexact f mode a)
  inexact := decide (SqrtInexact f mode a)

theorem sqrtOverflows_iff (f : Format) (mode : RoundingMode) {a : ℚ} (ha : 0 ≤ a) :
    SqrtOverflows f mode a ↔ Overflows f mode (Real.sqrt (a : ℝ)) := by
  unfold SqrtOverflows Overflows
  rw [roundUnbounded_sqrt f mode ha, abs_of_nonneg (by exact_mod_cast sqrtRoundUnbounded_nonneg f mode ha),
    ← maxFinite_ratCast (L := ℝ), Rat.cast_lt]

theorem sqrtInexact_iff (f : Format) (mode : RoundingMode) {a : ℚ} (ha : 0 ≤ a) :
    SqrtInexact f mode a ↔ Inexact f mode (Real.sqrt (a : ℝ)) := by
  rw [inexact_iff_overflows_or, SqrtInexact, sqrtOverflows_iff f mode ha,
    roundGradual_sqrt f mode ha]
  apply or_congr_right
  have hr : (0 : ℝ) ≤ (sqrtRoundGradual f mode a : ℚ) := by
    exact_mod_cast sqrtRoundGradual_nonneg f mode ha
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  rw [ne_eq, ne_eq, not_iff_not, @eq_comm ℝ, Real.sqrt_eq_iff_mul_self_eq haR hr]
  constructor
  · intro h
    have h' := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at h'
    exact h'.symm
  · intro h
    exact_mod_cast h.symm

theorem sqrtTiny_iff (f : Format) (tininess : Tininess) (mode : RoundingMode) {a : ℚ}
    (ha : 0 ≤ a) : SqrtTiny f tininess mode a ↔ Tiny f tininess mode (Real.sqrt (a : ℝ)) := by
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hne : a ≠ 0 ↔ Real.sqrt (a : ℝ) ≠ 0 := by
    rw [ne_eq, ne_eq, Real.sqrt_eq_zero haR, Rat.cast_eq_zero]
  unfold SqrtTiny Tiny
  apply and_congr hne
  cases tininess with
  | beforeRounding =>
    simp only [tininessMagnitude]
    have hsq : ((2 : ℝ) ^ emin f) ^ 2 = (((2 : ℚ) ^ (2 * emin f) : ℚ) : ℝ) := by
      rw [two_zpow_ratCast, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_lt' (two_zpow_pos _), hsq, Rat.cast_lt]
  | afterRounding =>
    simp only [tininessMagnitude]
    rw [roundUnbounded_sqrt f mode ha,
      abs_of_nonneg (by exact_mod_cast sqrtRoundUnbounded_nonneg f mode ha),
      ← two_zpow_ratCast (L := ℝ), Rat.cast_lt]

/-- The computable square-root classification equals the classification of the
real square root. -/
theorem sqrtRoundingFlags_eq (f : Format) (mode : RoundingMode) (tininess : Tininess) {a : ℚ}
    (ha : 0 ≤ a) :
    sqrtRoundingFlags f mode tininess a = roundingFlags f mode tininess (Real.sqrt (a : ℝ)) := by
  unfold sqrtRoundingFlags roundingFlags Underflows
  congr 1
  · exact decide_eq_decide.mpr (sqrtOverflows_iff f mode ha)
  · exact decide_eq_decide.mpr (and_congr (sqrtTiny_iff f tininess mode ha) (sqrtInexact_iff f mode ha))
  · exact decide_eq_decide.mpr (sqrtInexact_iff f mode ha)

end Silmaril.Numeric.Ieee754.FlagSpec
