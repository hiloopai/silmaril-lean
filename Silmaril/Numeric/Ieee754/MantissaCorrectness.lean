module

public import Silmaril.Numeric.Ieee754.Rounding
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Correctness of the IEEE significand rounding decision

The specification in this module is independent of the implementation's
case distinction on residual bits. Nearest rounding minimizes distance in an
ordered field over **every** natural-number significand; the directed modes select
the greatest lower or least upper integer. Equal-distance alternatives are
resolved by even parity or by larger magnitude, respectively.

`roundMantissa_correct` proves IEEE 754-2019 §4.3 for all five directions and
both signs, provided that `AccuracySound` relates the residual classification
to the exact magnitude. This is a component theorem: connecting residual-bit
shifts, format bounds, subnormals, and overflow to the specification requires
separate proofs. It is not a claim of complete IEEE conformance.

Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model.UnpackedFloat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Soundness of the residual classification with respect to an exact magnitude
in an ordered field. Inexact values lie strictly between consecutive integers. -/
def AccuracySound (mantissa : Nat) (accuracy : Accuracy) (q : K) : Prop :=
  match accuracy with
  | .exact => q = mantissa
  | .inexact order => (mantissa : K) < q ∧ q < mantissa + 1 ∧
      match order with
      | .lt => q < mantissa + 1 / 2
      | .eq => q = mantissa + 1 / 2
      | .gt => mantissa + 1 / 2 < q

/-- A globally nearest nonnegative integer, measured using absolute distance. -/
def NearestMagnitude (q : K) (result : Nat) : Prop :=
  ∀ candidate : Nat, |q - result| ≤ |q - candidate|

/-- Greatest integer magnitude no larger than the exact magnitude. -/
def LowerMagnitude (q : K) (result : Nat) : Prop :=
  (result : K) ≤ q ∧ ∀ candidate : Nat, (candidate : K) ≤ q → candidate ≤ result

/-- Least integer magnitude no smaller than the exact magnitude. -/
def UpperMagnitude (q : K) (result : Nat) : Prop :=
  q ≤ result ∧ ∀ candidate : Nat, q ≤ (candidate : K) → result ≤ candidate

/-- Independent IEEE rounding specification for a nonnegative magnitude and
its sign. Distance minimization ranges over all integer magnitudes, not merely
the two adjacent candidates. -/
def MantissaRounds (mode : RoundingMode) (sign : Sign) (q : K) (result : Nat) : Prop :=
  match mode with
  | .nearestTiesToEven => NearestMagnitude q result ∧
      ∀ candidate : Nat, |q - result| = |q - candidate| →
        result % 2 = 0 ∨ candidate = result
  | .nearestTiesToAway => NearestMagnitude q result ∧
      ∀ candidate : Nat, |q - result| = |q - candidate| → candidate ≤ result
  | .towardZero => LowerMagnitude q result
  | .towardPositive => if sign = .positive then UpperMagnitude q result else LowerMagnitude q result
  | .towardNegative => if sign = .negative then UpperMagnitude q result else LowerMagnitude q result

/-- Sound residuals always describe the interval beginning at the truncated magnitude. -/
theorem AccuracySound.bounds {n : Nat} {accuracy : Accuracy} {q : K}
    (sound : AccuracySound n accuracy q) : (n : K) ≤ q ∧ q < n + 1 := by
  cases accuracy with
  | exact =>
    change q = n at sound
    subst q
    exact ⟨le_rfl, by simp⟩
  | inexact _ => exact ⟨sound.1.le, sound.2.1⟩

theorem AccuracySound.nonneg {n : Nat} {accuracy : Accuracy} {q : K}
    (sound : AccuracySound n accuracy q) : 0 ≤ q :=
  le_trans (Nat.cast_nonneg n) sound.bounds.1

theorem lowerMagnitude_of_interval {n : Nat} {q : K}
    (hl : (n : K) ≤ q) (hu : q < n + 1) : LowerMagnitude q n := by
  refine ⟨hl, fun k hk => ?_⟩
  have : (k : K) < n + 1 := lt_of_le_of_lt hk hu
  have : k < n + 1 := by exact_mod_cast this
  omega

theorem upperMagnitude_of_interval {n : Nat} {q : K}
    (hl : (n : K) < q) (hu : q ≤ n + 1) : UpperMagnitude q (n + 1) := by
  refine ⟨by exact_mod_cast hu, fun k hk => ?_⟩
  have : (n : K) < k := lt_of_lt_of_le hl hk
  have : n < k := by exact_mod_cast this
  omega

theorem nearestMagnitude_lower {n : Nat} {q : K}
    (hl : (n : K) ≤ q) (hm : q ≤ n + 1 / 2) : NearestMagnitude q n := by
  intro k
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  by_cases hk : k ≤ n
  · have hkq : (k : K) ≤ n := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith : 0 ≤ q - k)]
    linarith
  · have hkq : (n : K) + 1 ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
    rw [abs_of_nonpos (by linarith : q - k ≤ 0)]
    linarith

theorem nearestMagnitude_upper {n : Nat} {q : K}
    (hm : (n : K) + 1 / 2 ≤ q) (hu : q ≤ n + 1) :
    NearestMagnitude q (n + 1) := by
  intro k
  simp only [Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonpos (by linarith : q - (n + 1) ≤ 0)]
  by_cases hk : k ≤ n
  · have hkq : (k : K) ≤ n := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith : 0 ≤ q - k)]
    linarith
  · have hkq : (n : K) + 1 ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
    rw [abs_of_nonpos (by linarith : q - k ≤ 0)]
    linarith

/-- A second nearest candidate to the lower endpoint exists only at the midpoint. -/
theorem lower_tie {n k : Nat} {q : K} (hl : (n : K) ≤ q)
    (hm : q ≤ n + 1 / 2) (tie : |q - n| = |q - k|) :
    k = n ∨ (q = n + 1 / 2 ∧ k = n + 1) := by
  rw [abs_of_nonneg (sub_nonneg.mpr hl)] at tie
  by_cases hk : k ≤ n
  · have hkq : (k : K) ≤ n := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith : 0 ≤ q - k)] at tie
    left
    have : (k : K) = n := by linarith
    exact_mod_cast this
  · have hkq : (n : K) + 1 ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
    rw [abs_of_nonpos (by linarith : q - k ≤ 0)] at tie
    right
    constructor
    · linarith
    · have : (k : K) = n + 1 := by linarith
      exact_mod_cast this

/-- A second nearest candidate to the upper endpoint exists only at the midpoint. -/
theorem upper_tie {n k : Nat} {q : K} (hm : (n : K) + 1 / 2 ≤ q)
    (hu : q ≤ n + 1) (tie : |q - (n + 1 : Nat)| = |q - k|) :
    k = n + 1 ∨ (q = n + 1 / 2 ∧ k = n) := by
  simp only [Nat.cast_add, Nat.cast_one] at tie
  rw [abs_of_nonpos (by linarith : q - (n + 1) ≤ 0)] at tie
  by_cases hk : k ≤ n
  · have hkq : (k : K) ≤ n := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith : 0 ≤ q - k)] at tie
    right
    constructor
    · linarith
    · have : (k : K) = n := by linarith
      exact_mod_cast this
  · have hkq : (n : K) + 1 ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
    rw [abs_of_nonpos (by linarith : q - k ≤ 0)] at tie
    left
    have : (k : K) = n + 1 := by linarith
    exact_mod_cast this

theorem nearestEven_lower_strict {n : Nat} {q : K} (sign : Sign)
    (hl : (n : K) ≤ q) (hm : q < n + 1 / 2) :
    MantissaRounds .nearestTiesToEven sign q n := by
  refine ⟨nearestMagnitude_lower hl hm.le, ?_⟩
  intro k hk
  rcases lower_tie hl hm.le hk with heq | ⟨heq, _⟩
  · exact Or.inr heq
  · linarith

theorem nearestEven_upper_strict {n : Nat} {q : K} (sign : Sign)
    (hm : (n : K) + 1 / 2 < q) (hu : q ≤ n + 1) :
    MantissaRounds .nearestTiesToEven sign q (n + 1) := by
  refine ⟨nearestMagnitude_upper hm.le hu, ?_⟩
  intro k hk
  rcases upper_tie hm.le hu hk with heq | ⟨heq, _⟩
  · exact Or.inr heq
  · linarith

theorem nearestAway_lower_strict {n : Nat} {q : K} (sign : Sign)
    (hl : (n : K) ≤ q) (hm : q < n + 1 / 2) :
    MantissaRounds .nearestTiesToAway sign q n := by
  refine ⟨nearestMagnitude_lower hl hm.le, ?_⟩
  intro k hk
  rcases lower_tie hl hm.le hk with heq | ⟨heq, _⟩
  · omega
  · linarith

theorem nearestAway_upper {n : Nat} {q : K} (sign : Sign)
    (hm : (n : K) + 1 / 2 ≤ q) (hu : q ≤ n + 1) :
    MantissaRounds .nearestTiesToAway sign q (n + 1) := by
  refine ⟨nearestMagnitude_upper hm hu, ?_⟩
  intro k hk
  rcases upper_tie hm hu hk with heq | ⟨_, heq⟩ <;> omega

theorem exact_mantissaRounds (mode : RoundingMode) (sign : Sign) (n : Nat) :
    MantissaRounds mode sign (n : K) n := by
  have hlo : LowerMagnitude (n : K) n := ⟨le_rfl, fun k hk => by exact_mod_cast hk⟩
  have hup : UpperMagnitude (n : K) n := ⟨le_rfl, fun k hk => by exact_mod_cast hk⟩
  have hnear : NearestMagnitude (n : K) n := by intro k; simp
  have heq (k : Nat) (h : |(n : K) - n| = |(n : K) - k|) : k = n := by
    have hzero : (n : K) - k = 0 := by simpa using h.symm
    have : (n : K) = k := sub_eq_zero.mp hzero
    exact_mod_cast this.symm
  cases mode with
  | nearestTiesToEven => exact ⟨hnear, fun k hk => Or.inr (heq k hk)⟩
  | nearestTiesToAway => exact ⟨hnear, fun k hk => Nat.le_of_eq (heq k hk)⟩
  | towardZero => exact hlo
  | towardPositive => cases sign <;> simp [MantissaRounds, hlo, hup]
  | towardNegative => cases sign <;> simp [MantissaRounds, hlo, hup]

/-- The local rounding decision chooses one of the bracketing magnitudes. -/
theorem roundMantissa_bracket (mode : RoundingMode) (sign : Sign) (n : Nat)
    (accuracy : Accuracy) :
    Rounding.roundMantissa mode sign n accuracy = n ∨
      Rounding.roundMantissa mode sign n accuracy = n + 1 := by
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  cases accuracy with
  | exact => exact Or.inl rfl
  | inexact order =>
    cases mode <;> cases sign <;> cases order <;>
      simp [Rounding.roundMantissa, Accuracy.roundToNearestEven] <;> omega

/-- IEEE's rounding direction is implemented correctly for every exact magnitude
in an ordered field satisfying the residual classification. -/
theorem roundMantissa_correct (mode : RoundingMode) (sign : Sign) (n : Nat)
    (accuracy : Accuracy) (q : K) (sound : AccuracySound n accuracy q) :
    MantissaRounds mode sign q (Rounding.roundMantissa mode sign n accuracy) := by
  cases accuracy with
  | exact =>
    change q = n at sound
    subst q
    exact exact_mantissaRounds mode sign n
  | inexact order =>
    obtain ⟨hl, hu, hmid⟩ := sound
    have hlo := lowerMagnitude_of_interval hl.le hu
    have hup := upperMagnitude_of_interval hl hu.le
    cases mode with
    | towardZero => exact hlo
    | towardPositive =>
      cases sign <;> simpa [Rounding.roundMantissa, MantissaRounds] using (by assumption)
    | towardNegative =>
      cases sign <;> simpa [Rounding.roundMantissa, MantissaRounds] using (by assumption)
    | nearestTiesToAway =>
      cases order with
      | lt => exact nearestAway_lower_strict sign hl.le hmid
      | eq =>
        exact nearestAway_upper sign (by simp [hmid]) hu.le
      | gt => exact nearestAway_upper sign hmid.le hu.le
    | nearestTiesToEven =>
      cases order with
      | lt => exact nearestEven_lower_strict sign hl.le hmid
      | gt => exact nearestEven_upper_strict sign hmid hu.le
      | eq =>
        have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases hmod with heven | hodd
        · simp only [Rounding.roundMantissa, Accuracy.roundToNearestEven, heven, Nat.add_zero]
          exact ⟨nearestMagnitude_lower hl.le (by simp [hmid]), fun _ _ => Or.inl heven⟩
        · simp only [Rounding.roundMantissa, Accuracy.roundToNearestEven, hodd]
          exact ⟨nearestMagnitude_upper (by simp [hmid]) hu.le,
            fun _ _ => Or.inl (by omega)⟩

/-- Every rounding direction has absolute error strictly below one unit of the
integer significand grid. The units here precede multiplication by the exponent. -/
theorem roundMantissa_error_lt_one (mode : RoundingMode) (sign : Sign) (n : Nat)
    (accuracy : Accuracy) (q : K) (sound : AccuracySound n accuracy q) :
    |q - Rounding.roundMantissa mode sign n accuracy| < 1 := by
  cases accuracy with
  | exact =>
    change q = n at sound
    simp [Rounding.roundMantissa, sound]
  | inexact order =>
    obtain ⟨hl, hu, _⟩ := sound
    rcases roundMantissa_bracket mode sign n (.inexact order) with heq | heq
    · rw [heq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · rw [heq]
      simp only [Nat.cast_add, Nat.cast_one]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩

end Silmaril.Numeric.Ieee754.Conformance
