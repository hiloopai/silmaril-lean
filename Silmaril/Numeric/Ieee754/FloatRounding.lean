module

public import Silmaril.Numeric.Ieee754.RoundingCorrectness
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Global optimality among binary floating-point magnitudes

The candidate set here is independent of the rounding implementation: every
bounded integer significand at every exponent at least the minimum subnormal
exponent is allowed. The upper exponent is deliberately unbounded, so overflow
is a subsequent encoding obligation.

Nearest optimality is global over this candidate set, rather than restricted
to the single exponent grid used by the implementation. Directed optimality
likewise quantifies over every representable magnitude. Midpoint tie choices
remain specified by the separate `RoundsOnGrid` certificate.

The final theorems cover every finite dyadic input and all five rounding
directions. They do not supply global optimality certificates for irrational
square roots or non-dyadic division results. The packed corollary requires an
explicit absence of exponent overflow after rounding.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model Float.Model.UnpackedFloat

/-- Binary magnitudes with the destination precision and gradual underflow,
but no upper exponent bound. Noncanonical duplicate representations are allowed. -/
def BinaryRepresentable (format : Format) (q : ℚ) : Prop :=
  ∃ mantissa : Nat, ∃ exponent : Int, mantissa < 2 ^ format.mantissaBits ∧
    format.minExponent ≤ exponent ∧ q = (mantissa : ℚ) * (2 : ℚ) ^ exponent

/-- Global nearest magnitude; midpoint preference is a separate property. -/
def NearestBinary (format : Format) (q result : ℚ) : Prop :=
  ∀ candidate, BinaryRepresentable format candidate → |q - result| ≤ |q - candidate|

/-- Greatest representable magnitude at or below the exact magnitude. -/
def LowerBinary (format : Format) (q result : ℚ) : Prop :=
  result ≤ q ∧ ∀ candidate, BinaryRepresentable format candidate → candidate ≤ q → candidate ≤ result

/-- Least representable magnitude at or above the exact magnitude. -/
def UpperBinary (format : Format) (q result : ℚ) : Prop :=
  q ≤ result ∧ ∀ candidate, BinaryRepresentable format candidate → q ≤ candidate → result ≤ candidate

/-- Global optimality in the selected direction, without claiming the nearest
midpoint preference from this predicate alone. -/
def BinaryOptimal (format : Format) (mode : RoundingMode) (sign : Sign)
    (q result : ℚ) : Prop :=
  BinaryRepresentable format result ∧ match mode with
  | .nearestTiesToEven | .nearestTiesToAway => NearestBinary format q result
  | .towardZero => LowerBinary format q result
  | .towardPositive => if sign = .positive then UpperBinary format q result else LowerBinary format q result
  | .towardNegative => if sign = .negative then UpperBinary format q result else LowerBinary format q result

theorem abs_dyadic_sign (sign : Sign) (mantissa : Nat) (exponent : Int) :
    |dyadic (sign.apply mantissa) exponent| = (mantissa : ℚ) * (2 : ℚ) ^ exponent := by
  cases sign <;> simp [dyadic, Sign.apply, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℚ) < 2) _)]

/-- A finite normalized result's magnitude is in the independent candidate set. -/
theorem normalized_value_representable (format : Format) (value : UnpackedFloat) (q : ℚ)
    (normalized : ExponentNormalized format value) (hv : value? value = some q) :
    BinaryRepresentable format |q| := by
  cases value with
  | notANumber | infinity _ => simp [value?] at hv
  | zero sign =>
    have hq : q = 0 := by simpa [value?] using hv.symm
    refine ⟨0, format.minExponent, Nat.pow_pos (by decide), le_rfl, ?_⟩
    simp [hq]
  | finite sign mantissa exponent hm =>
    have hq : q = dyadic (sign.apply mantissa) exponent := by simpa [value?] using hv.symm
    have hb := normalized.finite_bounds format sign mantissa exponent hm
    refine ⟨mantissa, exponent, hb.2.1, hb.1, ?_⟩
    rw [hq, abs_dyadic_sign]

/-- A representation with an exponent above the selected grid lies on that
grid exactly; no rounding is needed to align its integer significand. -/
theorem onGrid_of_exponent_ge (mantissa : Nat) (exponent target : Int) (he : target ≤ exponent) :
    ∃ k : Nat, (mantissa : ℚ) * (2 : ℚ) ^ exponent = (k : ℚ) * (2 : ℚ) ^ target := by
  refine ⟨(decreaseExponent mantissa exponent target).1, ?_⟩
  simpa only [dyadic, Sign.apply, Int.cast_natCast] using
    (decreaseExponent_value_of_le .positive mantissa he).symm

/-- Any candidate using a finer exponent lies strictly below the leading-bit
boundary of the coarser grid. -/
theorem below_boundary_of_exponent_lt (format : Format) (mantissa : Nat)
    (exponent target : Int) (hm : mantissa < 2 ^ format.mantissaBits) (he : exponent < target) :
    (mantissa : ℚ) * (2 : ℚ) ^ exponent <
      ((2 ^ (format.mantissaBits - 1) : Nat) : ℚ) * (2 : ℚ) ^ target := by
  have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
  have hm : (mantissa : ℚ) < (2 : ℚ) ^ format.mantissaBits := by exact_mod_cast hm
  have hpow : (2 : ℚ) ^ (exponent + 1) ≤ (2 : ℚ) ^ target :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpower : (2 : ℚ) ^ format.mantissaBits = 2 ^ (format.mantissaBits - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  calc
    (mantissa : ℚ) * (2 : ℚ) ^ exponent < 2 ^ format.mantissaBits * 2 ^ exponent :=
      mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
    _ = 2 ^ (format.mantissaBits - 1) * 2 ^ (exponent + 1) := by
      rw [hpower, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      simp only [zpow_one]
      ring
    _ ≤ 2 ^ (format.mantissaBits - 1) * 2 ^ target :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) _)
    _ = _ := by simp

/-- Above the minimum subnormal exponent, the exact input lies at or above
the selected grid's leading-bit boundary. -/
theorem selectedGrid_boundary_le (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa)
    (hnormal : format.minExponent < format.targetExponent (totalExponent mantissa exponent)) :
    ((2 ^ (format.mantissaBits - 1) : Nat) : ℚ) *
        (2 : ℚ) ^ format.targetExponent (totalExponent mantissa exponent) ≤
      (mantissa : ℚ) * (2 : ℚ) ^ exponent := by
  have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
  have ht : format.targetExponent (totalExponent mantissa exponent) =
      (mantissa.log2 : Int) + 1 + exponent - format.mantissaBits := by
    unfold Format.targetExponent totalExponent at *
    omega
  have he : ((format.mantissaBits - 1 : Nat) : Int) +
      format.targetExponent (totalExponent mantissa exponent) = (mantissa.log2 : Int) + exponent := by
    rw [ht]
    omega
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← zpow_natCast (2 : ℚ) (format.mantissaBits - 1),
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), he,
    zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos (by norm_num) _))
  exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hm)

/-- Candidates absent from the selected grid are strictly below its leading
boundary, which itself is no greater than the exact input. -/
theorem representable_grid_or_below (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa) (candidate : ℚ) (hc : BinaryRepresentable format candidate) :
    let target := format.targetExponent (totalExponent mantissa exponent)
    (∃ k : Nat, candidate = (k : ℚ) * (2 : ℚ) ^ target) ∨
      (candidate < ((2 ^ (format.mantissaBits - 1) : Nat) : ℚ) * (2 : ℚ) ^ target ∧
        ((2 ^ (format.mantissaBits - 1) : Nat) : ℚ) * (2 : ℚ) ^ target ≤
          (mantissa : ℚ) * (2 : ℚ) ^ exponent) := by
  obtain ⟨m, e, hprec, he, rfl⟩ := hc
  by_cases ht : format.targetExponent (totalExponent mantissa exponent) ≤ e
  · exact Or.inl (onGrid_of_exponent_ge m e _ ht)
  · right
    have hlt : e < format.targetExponent (totalExponent mantissa exponent) := by omega
    exact ⟨below_boundary_of_exponent_lt format m e _ hprec hlt,
      selectedGrid_boundary_le format mantissa exponent hm (by omega)⟩

/-- Scaling rational distance by the positive grid spacing preserves it. -/
theorem grid_distance_scale (q : ℚ) (mantissa : Nat) (exponent : Int) :
    |q / (2 : ℚ) ^ exponent - mantissa| * (2 : ℚ) ^ exponent =
      |q - (mantissa : ℚ) * (2 : ℚ) ^ exponent| := by
  have hp : 0 < (2 : ℚ) ^ exponent := zpow_pos (by norm_num) _
  calc
    |q / (2 : ℚ) ^ exponent - mantissa| * (2 : ℚ) ^ exponent =
        |(q / (2 : ℚ) ^ exponent - mantissa) * (2 : ℚ) ^ exponent| := by
      rw [abs_mul, abs_of_pos hp]
    _ = _ := by
      congr 1
      field_simp

/-- Nearest optimality on the selected grid implies nearest optimality over
every representable binary magnitude, including those on finer grids. -/
theorem nearestBinary_of_grid (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa) (rounded : Nat)
    (nearest : NearestMagnitude
      (((mantissa : ℚ) * (2 : ℚ) ^ exponent) /
        (2 : ℚ) ^ format.targetExponent (totalExponent mantissa exponent)) rounded) :
    NearestBinary format ((mantissa : ℚ) * (2 : ℚ) ^ exponent)
      ((rounded : ℚ) * (2 : ℚ) ^ format.targetExponent (totalExponent mantissa exponent)) := by
  let target := format.targetExponent (totalExponent mantissa exponent)
  let q := (mantissa : ℚ) * (2 : ℚ) ^ exponent
  have hp : 0 < (2 : ℚ) ^ target := zpow_pos (by norm_num) _
  have grid (k : Nat) : |q - (rounded : ℚ) * (2 : ℚ) ^ target| ≤
      |q - (k : ℚ) * (2 : ℚ) ^ target| := by
    have h := mul_le_mul_of_nonneg_right (nearest k) hp.le
    change |q / (2 : ℚ) ^ target - rounded| * (2 : ℚ) ^ target ≤
      |q / (2 : ℚ) ^ target - k| * (2 : ℚ) ^ target at h
    simpa only [grid_distance_scale] using h
  intro candidate hc
  rcases representable_grid_or_below format mantissa exponent hm candidate hc with
    ⟨k, hk⟩ | ⟨hbelow, hboundary⟩
  · rw [hk]
    exact grid k
  · calc
      _ ≤ |q - ((2 ^ (format.mantissaBits - 1) : Nat) : ℚ) * (2 : ℚ) ^ target| := grid _
      _ ≤ _ := by
        change candidate < ((2 ^ (format.mantissaBits - 1) : Nat) : ℚ) * (2 : ℚ) ^ target at hbelow
        change ((2 ^ (format.mantissaBits - 1) : Nat) : ℚ) * (2 : ℚ) ^ target ≤ q at hboundary
        rw [abs_of_nonneg (sub_nonneg.mpr hboundary),
          abs_of_nonneg (sub_nonneg.mpr (le_trans hbelow.le hboundary))]
        linarith

/-- The greatest grid value below the input is also the greatest value below
it among all representable binary magnitudes. -/
theorem lowerBinary_of_grid (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa) (rounded : Nat)
    (lower : LowerMagnitude
      (((mantissa : ℚ) * (2 : ℚ) ^ exponent) /
        (2 : ℚ) ^ format.targetExponent (totalExponent mantissa exponent)) rounded) :
    LowerBinary format ((mantissa : ℚ) * (2 : ℚ) ^ exponent)
      ((rounded : ℚ) * (2 : ℚ) ^ format.targetExponent (totalExponent mantissa exponent)) := by
  let target := format.targetExponent (totalExponent mantissa exponent)
  let q := (mantissa : ℚ) * (2 : ℚ) ^ exponent
  have hp : 0 < (2 : ℚ) ^ target := zpow_pos (by norm_num) _
  have grid (k : Nat) (hk : (k : ℚ) * (2 : ℚ) ^ target ≤ q) :
      (k : ℚ) * (2 : ℚ) ^ target ≤ (rounded : ℚ) * (2 : ℚ) ^ target := by
    have hk := lower.2 k ((le_div_iff₀ hp).mpr hk)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hp.le
  refine ⟨(le_div_iff₀ hp).mp lower.1, ?_⟩
  intro candidate hc hcandidate
  rcases representable_grid_or_below format mantissa exponent hm candidate hc with
    ⟨k, hk⟩ | ⟨hbelow, hboundary⟩
  · rw [hk] at hcandidate ⊢
    exact grid k hcandidate
  · exact le_trans hbelow.le (grid _ hboundary)

/-- The least grid value above the input is also the least value above it
among all representable binary magnitudes. -/
theorem upperBinary_of_grid (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa) (rounded : Nat)
    (upper : UpperMagnitude
      (((mantissa : ℚ) * (2 : ℚ) ^ exponent) /
        (2 : ℚ) ^ format.targetExponent (totalExponent mantissa exponent)) rounded) :
    UpperBinary format ((mantissa : ℚ) * (2 : ℚ) ^ exponent)
      ((rounded : ℚ) * (2 : ℚ) ^ format.targetExponent (totalExponent mantissa exponent)) := by
  let target := format.targetExponent (totalExponent mantissa exponent)
  let q := (mantissa : ℚ) * (2 : ℚ) ^ exponent
  have hp : 0 < (2 : ℚ) ^ target := zpow_pos (by norm_num) _
  refine ⟨(div_le_iff₀ hp).mp upper.1, ?_⟩
  intro candidate hc hcandidate
  rcases representable_grid_or_below format mantissa exponent hm candidate hc with
    ⟨k, hk⟩ | ⟨hbelow, hboundary⟩
  · rw [hk] at hcandidate ⊢
    have hk := upper.2 k ((div_le_iff₀ hp).mpr hcandidate)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hp.le
  · linarith

/-- For every finite dyadic input, every rounding direction returns a value
optimal over all binary magnitudes with the destination precision and minimum
exponent. Midpoint preferences are certified separately by
`roundUnpacked_finite_correct`; the maximum exponent and overflow remain separate. -/
theorem roundUnpacked_finite_optimal (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa) :
    ∃ result : ℚ, BinaryOptimal format mode sign ((mantissa : ℚ) * (2 : ℚ) ^ exponent) result ∧
      value? (Rounding.roundUnpacked format mode (.finite sign mantissa exponent hm)) =
        some (signed (sign == .negative) result) := by
  obtain ⟨rounded, hround, hvalue⟩ := roundUnpacked_finite_correct format mode sign mantissa exponent hm
  let target := format.targetExponent (totalExponent mantissa exponent)
  let result := (rounded : ℚ) * (2 : ℚ) ^ target
  have hrepr : BinaryRepresentable format result := by
    have h := normalized_value_representable format _ _
      (roundUnpacked_normalized format mode (.finite sign mantissa exponent hm)) hvalue
    simpa only [abs_dyadic_sign] using h
  refine ⟨result, ⟨hrepr, ?_⟩, ?_⟩
  · cases mode with
    | nearestTiesToEven => exact nearestBinary_of_grid format mantissa exponent hm rounded hround.1
    | nearestTiesToAway => exact nearestBinary_of_grid format mantissa exponent hm rounded hround.1
    | towardZero => exact lowerBinary_of_grid format mantissa exponent hm rounded hround
    | towardPositive =>
      cases sign with
      | negative => exact lowerBinary_of_grid format mantissa exponent hm rounded hround
      | positive => exact upperBinary_of_grid format mantissa exponent hm rounded hround
    | towardNegative =>
      cases sign with
      | negative => exact upperBinary_of_grid format mantissa exponent hm rounded hround
      | positive => exact lowerBinary_of_grid format mantissa exponent hm rounded hround
  · cases sign <;> simpa [dyadic, Sign.apply, signed, result, target] using hvalue

/-- Global nearest/directed optimality survives encoding and decoding whenever
the rounded finite exponent is in range. Gradual underflow, signed zero,
significand carries, and all five rounding directions are included. -/
theorem packRounded_finite_optimal (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (inRange : NoExponentOverflow format
      (Rounding.roundUnpacked format mode (.finite sign mantissa exponent hm))) :
    ∃ result : ℚ, BinaryOptimal format mode sign ((mantissa : ℚ) * (2 : ℚ) ^ exponent) result ∧
      value? (UnpackedFloat.unpack format
        (Rounding.packRounded format mode (.finite sign mantissa exponent hm))) =
        some (signed (sign == .negative) result) := by
  rw [unpack_packRounded format mode _ inRange]
  exact roundUnpacked_finite_optimal format mode sign mantissa exponent hm

end Silmaril.Numeric.Ieee754.Conformance
