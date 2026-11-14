module

public import Silmaril.Numeric.Libm.Lattice.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Proofs of the libm lattice edges that need real arithmetic

Round-to-nearest-even is within half a spacing of its input, and an overflowing
round-to-nearest result is at least `2 ^ (emax + 1) - 2 ^ maxQuantum / 2` in
magnitude. Together they give the edge from correct rounding to the 1/2-ulp
global bound. -/

@[expose] public section

namespace Silmaril.Proofs.Numeric.Libm.Lattice

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec Silmaril.Numeric.Libm Float.Model

/-- Nearest-even integer rounding moves by at most one half. -/
theorem abs_roundInt_rne_sub_le (t : ℝ) :
    |((roundInt .nearestTiesToEven t : ℤ) : ℝ) - t| ≤ 1 / 2 := by
  have hf : Int.fract t = t - ⌊t⌋ := (Int.self_sub_floor t).symm
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  unfold roundInt
  split_ifs with ha hb hc <;> simp only [not_lt] at * <;> push_cast <;> rw [abs_le] <;>
    constructor <;> linarith

/-- Nearest-even rounding to multiples of `2 ^ q` moves by at most `2 ^ q / 2`. -/
theorem abs_roundAt_rne_sub_le (q : ℤ) (x : ℝ) :
    |roundAt .nearestTiesToEven q x - x| ≤ 2 ^ q / 2 := by
  have hp : (0 : ℝ) < 2 ^ q := two_zpow_pos q
  have h := abs_roundInt_rne_sub_le (x / 2 ^ q)
  have hsplit : roundAt .nearestTiesToEven q x - x =
      (((roundInt .nearestTiesToEven (x / 2 ^ q) : ℤ) : ℝ) - x / 2 ^ q) * 2 ^ q := by
    rw [roundAt, sub_mul, div_mul_cancel₀ _ hp.ne']
  rw [hsplit, abs_mul, abs_of_pos hp]
  nlinarith

/-- The binade below the overflow threshold is finite: `2 ^ emax ≤ maxFinite`. -/
theorem two_zpow_emax_le_maxFinite (f : Format) : (2 : ℝ) ^ emax f ≤ maxFinite f := by
  unfold maxFinite maxSignificand maxQuantum
  have hp := two_le_precision f
  have hsplit : (2 : ℝ) ^ emax f = 2 ^ (precision f - 1) * 2 ^ (emax f - (precision f - 1)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  have hsig : (2 : ℝ) ^ (precision f - 1) ≤ ((2 ^ f.mantissaBits - 1 : ℤ) : ℝ) := by
    have hn : (f.mantissaBits : ℤ) - 1 = ((f.mantissaBits - 1 : ℕ) : ℤ) := by
      unfold precision at hp
      omega
    unfold precision
    rw [hn, zpow_natCast]
    have hk : f.mantissaBits = (f.mantissaBits - 1) + 1 := by
      unfold precision at hp
      omega
    have h1 : (1 : ℝ) ≤ 2 ^ (f.mantissaBits - 1) := one_le_pow₀ (by norm_num)
    push_cast
    rw [hk, pow_succ]
    simp only [Nat.add_sub_cancel]
    linarith
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hsig (two_zpow_pos _).le

/-- A round-to-nearest overflow happens only within half a top-binade spacing of
`2 ^ (emax + 1)` or beyond it (IEEE 754-2019 §7.4). -/
theorem overflow_threshold (f : Format) {r : ℝ} (h : Overflows f .nearestTiesToEven r) :
    (2 : ℝ) ^ (emax f + 1) - |r| ≤ 1 / 2 * 2 ^ maxQuantum f := by
  have hmq : (0 : ℝ) < 2 ^ maxQuantum f := two_zpow_pos _
  have hbig : maxFinite f < |r| := maxFinite_lt_abs_of_overflows h
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hbig
    linarith [maxFinite_pos (K := ℝ) f]
  have hlo := two_zpow_leadingExponent_le hr0
  by_cases hcase : emax f + 1 ≤ leadingExponent r
  · have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcase
    linarith
  · -- The unbounded rounding `u` lies on the grid of `r`'s binade.
    have hu : maxFinite f < |roundUnbounded f .nearestTiesToEven r| := h
    set le := leadingExponent r with hle
    set uq := unboundedQuantum f r with huq
    have huq' : uq = le - (precision f - 1) := rfl
    have hhi : |r| < (2 : ℝ) ^ (le + 1) := abs_lt_two_zpow_leadingExponent r
    have hp := two_le_precision f
    -- `2 ^ (le + 1) = 2 ^ p * 2 ^ uq`, an integer multiple of the grid.
    have hgrid : (2 : ℝ) ^ (le + 1) = ((2 ^ f.mantissaBits : ℤ) : ℝ) * 2 ^ uq := by
      rw [huq', Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      unfold precision
      ring
    have hubound : |roundUnbounded f .nearestTiesToEven r| ≤ (2 : ℝ) ^ (le + 1) := by
      rw [hgrid]
      exact abs_roundAt_le _ _ _ (by rw [← hgrid]; exact hhi.le)
    -- Hence `le = emax`.
    have hle_eq : le = emax f := by
      by_contra hne
      have hlt : le + 1 ≤ emax f := by omega
      have h1 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlt
      have h2 := two_zpow_emax_le_maxFinite f
      linarith
    have huq_eq : uq = maxQuantum f := by
      rw [huq', hle_eq]
      rfl
    -- `u = n * 2 ^ maxQuantum` with `|n| ≥ 2 ^ p`.
    set n := roundInt .nearestTiesToEven (r / 2 ^ maxQuantum f) with hn
    have hu_eq : roundUnbounded f .nearestTiesToEven r = (n : ℝ) * 2 ^ maxQuantum f := by
      show roundAt _ uq r = _
      rw [huq_eq]
      rfl
    have habs_u : |roundUnbounded f .nearestTiesToEven r| = |(n : ℝ)| * 2 ^ maxQuantum f := by
      rw [hu_eq, abs_mul, abs_of_pos hmq]
    have hn_big : (2 : ℤ) ^ f.mantissaBits ≤ |n| := by
      have h3 : ((2 ^ f.mantissaBits - 1 : ℤ) : ℝ) * 2 ^ maxQuantum f < |(n : ℝ)| * 2 ^ maxQuantum f := by
        rw [← habs_u]
        exact hu
      have h4 : ((2 ^ f.mantissaBits - 1 : ℤ) : ℝ) < ((|n| : ℤ) : ℝ) := by
        rw [Int.cast_abs]
        exact lt_of_mul_lt_mul_right h3 hmq.le
      have h5 := Int.cast_lt.mp h4
      omega
    have htop : (2 : ℝ) ^ (emax f + 1) ≤ |roundUnbounded f .nearestTiesToEven r| := by
      rw [habs_u, ← hle_eq, hgrid, huq_eq, ← Int.cast_abs]
      exact mul_le_mul_of_nonneg_right (Int.cast_le.mpr hn_big) hmq.le
    have herr : |roundUnbounded f .nearestTiesToEven r - r| ≤ 2 ^ maxQuantum f / 2 := by
      have := abs_roundAt_rne_sub_le (maxQuantum f) r
      rwa [show roundUnbounded f .nearestTiesToEven r = roundAt .nearestTiesToEven (maxQuantum f) r
        from by rw [← huq_eq]; rfl]
    have := abs_sub_abs_le_abs_sub (roundUnbounded f .nearestTiesToEven r) r
    linarith

/-- Round-to-nearest delivers an infinity exactly on overflow. -/
theorem deliver_rne (f : Format) (r : ℝ) :
    deliver f .nearestTiesToEven r =
      if Overflows f .nearestTiesToEven r then .infinite (decide (r < 0))
      else .finite (roundGradual f .nearestTiesToEven r) := by
  unfold deliver
  simp [overflowsToInfinity]

/-- (d) → (c): a correctly rounded result is within half an ulp. -/
theorem ulpClose_half_of_roundsTo (f : Format) {r : ℝ} {y : Option (Rounded ℚ)}
    (h : RoundsTo f .nearestTiesToEven r y) : UlpClose f (1 / 2) r y := by
  unfold RoundsTo at h
  rw [deliver_rne] at h
  rcases y with _ | ⟨v⟩ | ⟨negative⟩
  · simp at h
  · simp only [Option.map_some, Option.some.injEq, Rounded.cast] at h
    split_ifs at h with ho
    have hv : (v : ℝ) = roundGradual f .nearestTiesToEven r := Rounded.finite.inj h
    show |(v : ℝ) - r| ≤ 1 / 2 * ulp f r
    rw [hv, ulp]
    have := abs_roundAt_rne_sub_le (quantum f r) r
    unfold roundGradual
    linarith
  · simp only [Option.map_some, Option.some.injEq, Rounded.cast] at h
    split_ifs at h with ho
    exact ⟨Rounded.infinite.inj h, overflow_threshold f ho⟩

end Silmaril.Proofs.Numeric.Libm.Lattice

namespace Silmaril.Proofs.Numeric.Libm.Lattice

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec Silmaril.Numeric.Libm Float.Model

theorem ulp_pos (f : Format) (r : ℝ) : 0 < ulp f r := two_zpow_pos _

theorem ulpClose_mono (f : Format) {k k' r : ℝ} {y : Option (Rounded ℚ)} (hk : k ≤ k')
    (h : UlpClose f k r y) : UlpClose f k' r y := by
  rcases y with _ | ⟨v⟩ | ⟨negative⟩
  · exact h
  · have := mul_le_mul_of_nonneg_right hk (ulp_pos f r).le
    exact le_trans (show |(v : ℝ) - r| ≤ k * ulp f r from h) this
  · obtain ⟨hn, hb⟩ := h
    exact ⟨hn, le_trans hb (mul_le_mul_of_nonneg_right hk (two_zpow_pos _).le)⟩

/-- The value of a finite encoding is a number of the format, over the reals. -/
theorem representable_real {τ : Type} [LibmFloat τ] {y : τ} {v : ℚ}
    (h : LibmFloat.rounded? y = some (.finite v)) :
    Representable (LibmFloat.format τ) (v : ℝ) := by
  obtain ⟨n, q, hv, hn, hq, hmax⟩ := LibmFloat.representable y v h
  refine ⟨n, q, ?_, hn, hq, ?_⟩
  · rw [hv]
    push_cast
    rfl
  · rw [← maxFinite_ratCast (L := ℝ), ← Rat.cast_abs]
    exact_mod_cast hmax

theorem cr_of_isExactly {τ : Type} [LibmFloat τ] {r : ℝ} {y : τ}
    (h : LibmFloat.IsExactly r y) : LibmFloat.CR r y := by
  obtain ⟨v, hv, rfl⟩ := h
  show (LibmFloat.rounded? y).map Rounded.cast = _
  rw [hv, deliver_of_representable _ _ (representable_real hv)]
  rfl

theorem nearCR_of_cr {τ : Type} [LibmFloat τ] {n r : ℝ} {y : τ} (hn : 0 ≤ n)
    (h : LibmFloat.CR r y) : LibmFloat.NearCR n r y := by
  unfold LibmFloat.CR RoundsTo at h
  unfold LibmFloat.NearCR CRDistance
  rcases hy : LibmFloat.rounded? y with _ | ⟨v⟩ | ⟨negative⟩ <;> rw [hy] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq, Rounded.cast] at h
    rw [← h]
    simp only [sub_self, abs_zero]
    exact mul_nonneg hn (ulp_pos _ _).le
  · simp only [Option.map_some, Option.some.injEq, Rounded.cast] at h
    rw [← h]

theorem nearCR_mono {τ : Type} [LibmFloat τ] {n n' r : ℝ} {y : τ} (hn : n ≤ n')
    (h : LibmFloat.NearCR n r y) : LibmFloat.NearCR n' r y := by
  unfold LibmFloat.NearCR CRDistance at *
  split at h
  · rename_i c v _ _
    exact le_trans h (mul_le_mul_of_nonneg_right hn (ulp_pos _ _).le)
  · exact h
  · exact h.elim

theorem cr_of_nearCR_zero {τ : Type} [LibmFloat τ] {r : ℝ} {y : τ}
    (h : LibmFloat.NearCR 0 r y) : LibmFloat.CR r y := by
  unfold LibmFloat.NearCR CRDistance at h
  unfold LibmFloat.CR RoundsTo
  split at h
  · rename_i c v hd hy
    rw [hy, hd]
    simp only [zero_mul, abs_nonpos_iff, sub_eq_zero] at h
    simp [Rounded.cast, h]
  · rename_i negative negative' hd hy
    rw [hy, hd, h]
    rfl
  · exact h.elim

end Silmaril.Proofs.Numeric.Libm.Lattice
