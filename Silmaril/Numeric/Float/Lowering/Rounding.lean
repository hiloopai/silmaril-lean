module

public import Silmaril.Numeric.Float.Wasm
public import Silmaril.Numeric.Ieee754.ConversionCorrectness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rounding depends only on the value, and on sticky bits (architecture-independent)

The core model rounds a finite `UnpackedFloat` given as a mantissa and an
exponent; one value has many such representations. This file proves the two
facts needed to verify multi-instruction conversions (for example unsigned
64-bit integer to binary32 or binary64 on an ISA with only signed conversions):

* `roundUnpacked_scale` and `roundUnpacked_congr`: the rounded result depends
  only on the sign and the rational value, not on the representation.
* `roundUnpacked_ofInt_sticky`: for a positive integer `n`, the rounded result
  depends only on `n / 2^j` and on whether `n % 2^j = 0`, as long as `j` is
  below the rounding position. This is the round-to-odd / sticky-bit argument
  that lets a sequence replace low-order bits by any nonzero pattern.

It also gives `roundUnpacked_exact`: a representable value is rounded to
itself, in canonical form.

All statements are about the executable rounding `Rounding.roundUnpacked` of
`Silmaril.Numeric.Ieee754.Rounding`, in every rounding direction, for every
format. Nothing here depends on an instruction set.
-/

@[expose] public section

namespace Silmaril.Numeric.Float.Lowering

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754 (RoundingMode)
open Silmaril.Numeric.Ieee754.Conformance (value? dyadic ExponentNormalized)

/-! ## Shifting extended mantissas -/

theorem shiftRight_def (em : ExtendedMantissa) (n : Nat) :
    em >>> n = Nat.repeat ExtendedMantissa.shiftRightOne n em := rfl

theorem shiftRight_zero (em : ExtendedMantissa) : em >>> 0 = em := rfl

theorem shiftRight_succ (em : ExtendedMantissa) (n : Nat) :
    em >>> (n + 1) = ExtendedMantissa.shiftRightOne (em >>> n) := rfl

theorem shiftRight_add (em : ExtendedMantissa) (a b : Nat) : em >>> (a + b) = (em >>> a) >>> b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, shiftRight_succ, ih, shiftRight_succ]

/-- Shifting out zero bits is exact. -/
theorem shiftRight_zeros (m k : Nat) :
    (⟨m * 2 ^ k, false, false⟩ : ExtendedMantissa) >>> k = ⟨m, false, false⟩ := by
  induction k generalizing m with
  | zero => simp [shiftRight_zero]
  | succ k ih =>
    rw [show k + 1 = k + 1 from rfl, shiftRight_succ,
      show m * 2 ^ (k + 1) = (2 * m) * 2 ^ k by rw [pow_succ]; ring, ih]
    simp [ExtendedMantissa.shiftRightOne]

/-- The closed form of a shift by at least one position. -/
theorem shiftRight_closed (n k : Nat) :
    (⟨n, false, false⟩ : ExtendedMantissa) >>> (k + 1) =
      ⟨n / 2 ^ (k + 1), n / 2 ^ k % 2 != 0, decide (n % 2 ^ k ≠ 0)⟩ := by
  induction k with
  | zero => simp [shiftRight_succ, shiftRight_zero, ExtendedMantissa.shiftRightOne, Nat.mod_one]
  | succ k ih =>
    rw [shiftRight_succ, ih]
    show ExtendedMantissa.mk _ _ _ = _
    congr 1
    · rw [Nat.div_div_eq_div_mul, ← pow_succ]
    · have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      rw [Nat.mod_pow_succ]
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with hb | hb
      · rw [hb]; simp
      · rw [hb]
        simp only [Nat.mul_one]
        exact (decide_eq_true (by omega)).symm

/-! ## Rounding is a function of the value -/

theorem log2_mul_pow (m k : Nat) (hm : m ≠ 0) : Nat.log2 (m * 2 ^ k) = Nat.log2 m + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.log2_two_mul (by positivity), ih]
    omega

theorem totalExponent_scale (m k : Nat) (e : Int) (hm : m ≠ 0) :
    totalExponent (m * 2 ^ k) (e - k) = totalExponent m e := by
  simp only [totalExponent, log2_mul_pow m k hm]
  push_cast
  omega

/-- `roundWithAccuracy` depends on its input only through the first shift. -/
theorem roundWithAccuracy_congr (fmt : Format) (mode : RoundingMode) (s : Sign) {m1 m2 : Nat}
    {e1 e2 : Int} {a1 a2 : Accuracy}
    (h : shiftToTargetExponent fmt m1 e1 a1 = shiftToTargetExponent fmt m2 e2 a2) :
    Silmaril.Numeric.Ieee754.Rounding.roundWithAccuracy fmt mode s m1 e1 a1 =
      Silmaril.Numeric.Ieee754.Rounding.roundWithAccuracy fmt mode s m2 e2 a2 := by
  unfold Silmaril.Numeric.Ieee754.Rounding.roundWithAccuracy
  rw [h]

private theorem shiftToTargetExponent_eq (fmt : Format) (M : Nat) (E T : Int)
    (hT : fmt.targetExponent (totalExponent M E) = T) :
    shiftToTargetExponent fmt M E .exact =
      ((⟨M, false, false⟩ : ExtendedMantissa) >>> (T - E).toNat, E + (T - E).toNat) := by
  simp only [shiftToTargetExponent, shiftToExponent, hT]
  rfl

/-- Scaling the mantissa by `2^k` and lowering the exponent by `k` does not change
the rounded result. -/
theorem roundUnpacked_scale (fmt : Format) (mode : RoundingMode) (s : Sign) (m : Nat) (e : Int)
    (k : Nat) (hm : 0 < m) (hmk : 0 < m * 2 ^ k) :
    Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite s (m * 2 ^ k) (e - k) hmk) =
      Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite s m e hm) := by
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hmk0 : m * 2 ^ k ≠ 0 := Nat.pos_iff_ne_zero.mp hmk
  simp only [Silmaril.Numeric.Ieee754.Rounding.roundUnpacked]
  rw [totalExponent_scale m k e hm0]
  set T := fmt.targetExponent (totalExponent m e) with hTdef
  apply roundWithAccuracy_congr
  -- both first shifts, with their recomputed target `T`
  have t1 := Silmaril.Numeric.Ieee754.Conformance.decreaseExponent_totalExponent (m * 2 ^ k) (e - k) T hmk0
  have t2 := Silmaril.Numeric.Ieee754.Conformance.decreaseExponent_totalExponent m e T hm0
  rw [totalExponent_scale m k e hm0] at t1
  rw [shiftToTargetExponent_eq fmt _ _ T (by rw [t1]), shiftToTargetExponent_eq fmt _ _ T (by rw [t2])]
  simp only [decreaseExponent, Nat.shiftLeft_eq]
  rcases le_or_gt T (e - k) with h1 | h1
  · -- no right shift at all
    have ha : (e - ↑k - T).toNat + k = (e - T).toNat := by omega
    rw [show (T - (e - ↑k - ↑(e - ↑k - T).toNat)).toNat = 0 by omega,
      show (T - (e - ↑(e - T).toNat)).toNat = 0 by omega]
    simp only [shiftRight_zero, Prod.mk.injEq, ExtendedMantissa.mk.injEq, and_true]
    refine ⟨?_, by omega⟩
    rw [← ha, pow_add]; ring
  · rcases le_or_gt T e with h2 | h2
    · -- the scaled form shifts out exactly its extra zero bits
      set j := (e - T).toNat with hj
      have hjk : j < k := by omega
      rw [show (e - ↑k - T).toNat = 0 by omega,
        show (T - (e - ↑k - ↑(0 : Nat))).toNat = k - j by omega,
        show (T - (e - ↑j)).toNat = 0 by omega]
      simp only [pow_zero, Nat.mul_one, shiftRight_zero]
      rw [show m * 2 ^ k = (m * 2 ^ j) * 2 ^ (k - j) by
        rw [Nat.mul_assoc, ← pow_add, Nat.add_sub_cancel' hjk.le], shiftRight_zeros]
      simp only [Prod.mk.injEq, true_and]
      omega
    · -- both shift right; the scaled form first drops its `k` zero bits
      rw [show (e - ↑k - T).toNat = 0 by omega, show (e - T).toNat = 0 by omega,
        show (T - (e - ↑k - ↑(0 : Nat))).toNat = k + (T - e).toNat by omega,
        show (T - (e - ↑(0 : Nat))).toNat = (T - e).toNat by omega]
      simp only [pow_zero, Nat.mul_one]
      rw [shiftRight_add, shiftRight_zeros]
      simp only [Prod.mk.injEq, true_and]
      omega

private theorem roundUnpacked_congr_le (fmt : Format) (mode : RoundingMode) (s : Sign)
    {m1 m2 : Nat} {e1 e2 : Int} (h1 : 0 < m1) (h2 : 0 < m2) (hv : (m1 : ℚ) * 2 ^ e1 = m2 * 2 ^ e2)
    (hle : e1 ≤ e2) :
    Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite s m1 e1 h1) =
      Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite s m2 e2 h2) := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, e2 = e1 + k := ⟨(e2 - e1).toNat, by omega⟩
  have hm : m1 = m2 * 2 ^ k := by
    have h2e : (2 : ℚ) ^ e2 = 2 ^ e1 * 2 ^ k := by
      rw [hk, zpow_add₀ (by norm_num), zpow_natCast]
    rw [h2e] at hv
    have hpos : (0 : ℚ) < 2 ^ e1 := zpow_pos (by norm_num) _
    have : (m1 : ℚ) = m2 * 2 ^ k := by
      have h' : (m1 : ℚ) * 2 ^ e1 = (m2 * 2 ^ k) * 2 ^ e1 := by rw [hv]; ring
      exact mul_right_cancel₀ (ne_of_gt hpos) h'
    exact_mod_cast this
  have he : e1 = e2 - k := by omega
  subst hm
  subst he
  exact roundUnpacked_scale fmt mode s m2 e2 k h2 h1

/-- Two representations of the same value round alike. -/
theorem roundUnpacked_congr (fmt : Format) (mode : RoundingMode) (s : Sign) {m1 m2 : Nat}
    {e1 e2 : Int} (h1 : 0 < m1) (h2 : 0 < m2) (hv : (m1 : ℚ) * 2 ^ e1 = m2 * 2 ^ e2) :
    Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite s m1 e1 h1) =
      Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite s m2 e2 h2) := by
  rcases le_total e1 e2 with hle | hle
  · exact roundUnpacked_congr_le fmt mode s h1 h2 hv hle
  · exact (roundUnpacked_congr_le fmt mode s h2 h1 hv.symm hle).symm

/-- A representable value rounds to itself: the result is the canonical finite
form of the same value. -/
theorem roundUnpacked_exact (fmt : Format) (mode : RoundingMode) (s : Sign) {M : Nat} {E : Int}
    (hM : 0 < M) {m0 : Nat} {e0 : Int} (h0 : 0 < m0) (hm0 : m0 < 2 ^ fmt.mantissaBits)
    (he0 : fmt.minExponent ≤ e0) (hv : (M : ℚ) * 2 ^ E = m0 * 2 ^ e0) :
    ∃ m' e' h', Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite s M E hM) =
      .finite s m' e' h' ∧ (m' : ℚ) * 2 ^ e' = m0 * 2 ^ e0 ∧ e' ≤ e0 := by
  rw [roundUnpacked_congr fmt mode s hM h0 hv]
  have ht : fmt.targetExponent (totalExponent m0 e0) ≤ e0 := by
    have hlog := (Nat.log2_lt (Nat.ne_of_gt h0)).mpr hm0
    simp only [Format.targetExponent, totalExponent]
    omega
  refine ⟨_, _, _, Silmaril.Numeric.Ieee754.Conformance.roundUnpacked_finite_of_target_le fmt mode s
    m0 e0 h0 ht, ?_, ht⟩
  set T := fmt.targetExponent (totalExponent m0 e0)
  have ha : (((e0 - T).toNat : Nat) : Int) = e0 - T := Int.toNat_of_nonneg (by omega)
  rw [Nat.shiftLeft_eq]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num), ha, show e0 - T + T = e0 by omega]

/-! ## Sticky bits of integers -/

theorem roundUnpacked_ofInt_pos (fmt : Format) (mode : RoundingMode) (n : Nat) (hn : 0 < n)
    (hT : 0 < fmt.targetExponent (totalExponent n 0)) :
    Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite .positive n 0 hn) =
      Silmaril.Numeric.Ieee754.Rounding.roundWithAccuracy fmt mode .positive n 0 .exact := by
  simp only [Silmaril.Numeric.Ieee754.Rounding.roundUnpacked, decreaseExponent]
  rw [show ((0 : Int) - fmt.targetExponent (totalExponent n 0)).toNat = 0 by omega]
  simp

theorem log2_eq_log2_div_add {n j : Nat} (h : 0 < n / 2 ^ j) :
    Nat.log2 n = Nat.log2 (n / 2 ^ j) + j := by
  have hq : n / 2 ^ j ≠ 0 := Nat.pos_iff_ne_zero.mp h
  have hn : n ≠ 0 := by
    intro h0; rw [h0, Nat.zero_div] at hq; exact hq rfl
  rw [Nat.log2_eq_iff hn]
  obtain ⟨h1, h2⟩ := (Nat.log2_eq_iff hq).mp rfl
  have hj : 0 < 2 ^ j := Nat.two_pow_pos j
  constructor
  · calc 2 ^ (Nat.log2 (n / 2 ^ j) + j) = 2 ^ Nat.log2 (n / 2 ^ j) * 2 ^ j := pow_add _ _ _
      _ ≤ n / 2 ^ j * 2 ^ j := Nat.mul_le_mul_right _ h1
      _ ≤ n := Nat.div_mul_le_self n _
  · have := Nat.lt_div_mul_add (a := n) hj
    calc n < n / 2 ^ j * 2 ^ j + 2 ^ j := this
      _ = (n / 2 ^ j + 1) * 2 ^ j := by ring
      _ ≤ 2 ^ (Nat.log2 (n / 2 ^ j) + 1) * 2 ^ j := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (Nat.log2 (n / 2 ^ j) + j + 1) := by rw [← pow_add]; congr 1; omega

/-- Two positive integers round alike when they agree above bit `j` and are
both or neither multiples of `2^j`, provided `j` is below the rounding position
(the first shift of `roundWithAccuracy` drops at least `j + 1` bits). -/
theorem roundUnpacked_ofInt_sticky (fmt : Format) (mode : RoundingMode) {n1 n2 : Nat} (j : Nat)
    (h1 : 0 < n1) (h2 : 0 < n2) (hdiv : n1 / 2 ^ j = n2 / 2 ^ j) (hj : 0 < n1 / 2 ^ j)
    (hmod : n1 % 2 ^ j = 0 ↔ n2 % 2 ^ j = 0)
    (hT : (j : Int) < fmt.targetExponent (totalExponent n1 0)) :
    Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite .positive n1 0 h1) =
      Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite .positive n2 0 h2) := by
  have hlog : Nat.log2 n1 = Nat.log2 n2 := by
    rw [log2_eq_log2_div_add (n := n1) hj, log2_eq_log2_div_add (n := n2) (hdiv ▸ hj), hdiv]
  have htot : totalExponent n1 0 = totalExponent n2 0 := by simp [totalExponent, hlog]
  set T := fmt.targetExponent (totalExponent n1 0) with hTdef
  rw [roundUnpacked_ofInt_pos fmt mode n1 h1 (by omega),
    roundUnpacked_ofInt_pos fmt mode n2 h2 (by rw [← htot]; omega)]
  apply roundWithAccuracy_congr
  rw [shiftToTargetExponent_eq fmt n1 0 T rfl, shiftToTargetExponent_eq fmt n2 0 T (by rw [← htot])]
  obtain ⟨t, ht⟩ : ∃ t : Nat, (T - 0).toNat = t + 1 := ⟨(T - 0).toNat - 1, by omega⟩
  have hjt : j ≤ t := by omega
  rw [ht, shiftRight_closed, shiftRight_closed]
  simp only [Prod.mk.injEq, and_true, ExtendedMantissa.mk.injEq]
  have split : ∀ n i, n / 2 ^ (j + i) = n / 2 ^ j / 2 ^ i := fun n i => by
    rw [pow_add, Nat.div_div_eq_div_mul]
  obtain ⟨i, rfl⟩ : ∃ i, t = j + i := ⟨t - j, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [show j + i + 1 = j + (i + 1) by omega, split, split, hdiv]
  · rw [split, split, hdiv]
  · have hm : ∀ n, n % 2 ^ (j + i) = n % 2 ^ j + 2 ^ j * (n / 2 ^ j % 2 ^ i) := fun n => by
      rw [pow_add, Nat.mod_mul]
    rw [hm, hm, hdiv]
    have hp : 0 < 2 ^ j := Nat.two_pow_pos j
    rw [Bool.eq_iff_iff]
    simp only [ne_eq, decide_eq_true_eq]
    constructor
    · intro h h'
      apply h
      have h0 : n2 % 2 ^ j = 0 := by omega
      have h00 : 2 ^ j * (n2 / 2 ^ j % 2 ^ i) = 0 := by omega
      rw [hmod.mpr h0, h00]
    · intro h h'
      apply h
      have h0 : n1 % 2 ^ j = 0 := by omega
      have h00 : 2 ^ j * (n2 / 2 ^ j % 2 ^ i) = 0 := by omega
      rw [hmod.mp h0, h00]

end Silmaril.Numeric.Float.Lowering
