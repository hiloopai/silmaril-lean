module

public import Silmaril.Numeric.Ieee754.Flags.Binary
public import Silmaril.Numeric.Ieee754.ArithmeticCorrectness
public import Silmaril.Numeric.Ieee754.IntegerRounding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Agreement with the executable rounding

The flag specification rounds with `roundGradual` and `deliver`, defined
directly from the rounding directions. The executable arithmetic of
`Numeric.Ieee754.Rounding` rounds with residual bits and shifts. This module
proves that the two agree: for every finite unpacked value `u` with rational
value `v`, the decoded result of `Rounding.packRounded format mode u` is
`deliver format mode v` (`roundedOf?_unpack_packRounded`). The proof uses the
existing grid certificate `roundUnpacked_finite_correct` and the packing
theorems, and shows that the executable's grid exponent is the specification's
`quantum`.

Consequently, for addition, subtraction, multiplication and fused multiply-add
on binary32 and binary64, the inexact flag holds exactly when the value returned
by `addWith`, `subWith`, `mulWith` or `fmaWith` differs from the exact rational
result (`F32.addFlags_inexact_iff` and siblings).

Integral rounding (`Rounding.integralRounded`, behind `roundIntegral`) delivers
`roundInt` of the exact value (`roundedOf?_unpack_integralRounded`), which is a
finite value of the format for binary32 and binary64 (`representable_roundInt`),
so the inexact flag of `roundToIntegralExact` holds exactly when the returned
value differs from the operand (`F32.roundToIntegralFlags_inexact_iff`).

Division and square root use separate quotient and root cores; they are
related to `deliver` in `Silmaril.Numeric.Ieee754.Flags.DivSqrt`.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model Float.Model.UnpackedFloat Conformance

/-! ## Rounding directions under negation -/

/-- The direction obtained by reflecting through zero. -/
def reflectMode : RoundingMode → RoundingMode
  | .towardPositive => .towardNegative
  | .towardNegative => .towardPositive
  | mode => mode

section Neg

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

private theorem ceil_eq_floor_add_one_of_fract_ne {x : K} (h : Int.fract x ≠ 0) :
    ⌈x⌉ = ⌊x⌋ + 1 := by
  have hpos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)
  have hx := Int.floor_add_fract x
  have hlt := Int.fract_lt_one x
  rw [Int.ceil_eq_iff]
  push_cast
  constructor <;> linarith

/-- Rounding the negation is the negation of rounding in the reflected
direction. -/
theorem roundInt_neg (mode : RoundingMode) (x : K) :
    roundInt mode (-x) = -roundInt (reflectMode mode) x := by
  by_cases hfr : Int.fract x = 0
  · have hx : x = (⌊x⌋ : K) := by
      have := Int.floor_add_fract x
      rw [hfr] at this
      linarith
    rw [hx, ← Int.cast_neg, roundInt_intCast, roundInt_intCast]
  have hceil := ceil_eq_floor_add_one_of_fract_ne hfr
  have hfloorNeg : ⌊-x⌋ = -⌊x⌋ - 1 := by rw [Int.floor_neg, hceil]; ring
  have hfractNeg : Int.fract (-x) = 1 - Int.fract x := Int.fract_neg hfr
  have hx := Int.floor_add_fract x
  cases mode with
  | towardZero =>
    simp only [roundInt, reflectMode]
    rcases lt_trichotomy x 0 with h | h | h
    · have h' : 0 ≤ -x := by linarith
      simp [h', not_le.mpr h, Int.floor_neg]
    · subst h
      simp
    · have h' : ¬ 0 ≤ -x := by linarith
      simp [h', h.le, Int.ceil_neg]
  | towardPositive => simp [roundInt, reflectMode, Int.ceil_neg]
  | towardNegative => simp [roundInt, reflectMode, Int.floor_neg]
  | nearestTiesToEven =>
    simp only [roundInt, reflectMode, hfloorNeg, hfractNeg]
    rcases lt_trichotomy (Int.fract x) (1 / 2) with h | h | h
    · have h1 : ¬ 1 - Int.fract x < 1 / 2 := by linarith
      have h2 : 1 / 2 < 1 - Int.fract x := by linarith
      simp only [h, h1, h2, ↓reduceIte]
      ring
    · have h1 : ¬ 1 - Int.fract x < 1 / 2 := by linarith
      have h2 : ¬ 1 / 2 < 1 - Int.fract x := by linarith
      have h3 : ¬ Int.fract x < 1 / 2 := by linarith
      have h4 : ¬ 1 / 2 < Int.fract x := by linarith
      simp only [h1, h2, h3, h4, ↓reduceIte]
      split_ifs <;> omega
    · have h1 : 1 - Int.fract x < 1 / 2 := by linarith
      have h3 : ¬ Int.fract x < 1 / 2 := by linarith
      simp only [h, h1, h3, ↓reduceIte]
      ring
  | nearestTiesToAway =>
    simp only [roundInt, reflectMode, hfloorNeg, hfractNeg]
    rcases lt_trichotomy (Int.fract x) (1 / 2) with h | h | h
    · have h1 : ¬ 1 - Int.fract x < 1 / 2 := by linarith
      have h2 : 1 / 2 < 1 - Int.fract x := by linarith
      simp only [h, h1, h2, ↓reduceIte]
      ring
    · have h1 : ¬ 1 - Int.fract x < 1 / 2 := by linarith
      have h2 : ¬ 1 / 2 < 1 - Int.fract x := by linarith
      have h3 : ¬ Int.fract x < 1 / 2 := by linarith
      have h4 : ¬ 1 / 2 < Int.fract x := by linarith
      simp only [h1, h2, h3, h4, ↓reduceIte]
      have hne : x ≠ 0 := by
        intro h0
        rw [h0, Int.fract_zero] at hfr
        exact hfr rfl
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have e1 : 0 ≤ -x := by linarith
        have e2 : ¬ 0 ≤ x := not_le.mpr hneg
        simp only [e1, e2, ↓reduceIte]
        ring
      · have e1 : ¬ 0 ≤ -x := by linarith
        have e2 : 0 ≤ x := hpos.le
        simp only [e1, e2, ↓reduceIte]
        ring
    · have h1 : 1 - Int.fract x < 1 / 2 := by linarith
      have h3 : ¬ Int.fract x < 1 / 2 := by linarith
      simp only [h, h1, h3, ↓reduceIte]
      ring

end Neg

/-! ## The significand specification selects `roundInt` -/

section Mantissa

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

omit [IsStrictOrderedRing K] in
private theorem floor_eq_of_lower {q : K} {n : ℕ} (h : LowerMagnitude q n) : ⌊q⌋ = n := by
  rw [Int.floor_eq_iff]
  refine ⟨by exact_mod_cast h.1, lt_of_not_ge fun hle => ?_⟩
  have := h.2 (n + 1) (by exact_mod_cast hle)
  omega

private theorem ceil_eq_of_upper {q : K} (hq : 0 ≤ q) {n : ℕ} (h : UpperMagnitude q n) :
    ⌈q⌉ = n := by
  rw [Int.ceil_eq_iff]
  refine ⟨lt_of_not_ge fun hle => ?_, by exact_mod_cast h.1⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    push_cast at hle
    linarith
  · have hle' : q ≤ ((n - 1 : ℕ) : K) := by
      rw [Nat.cast_sub hn]
      push_cast at hle ⊢
      linarith
    have := h.2 (n - 1) hle'
    omega

omit [IsStrictOrderedRing K] in
/-- A nearest integer is within one half of `q`. -/
private theorem abs_sub_le_half_of_nearest {q : K} (hq : 0 ≤ q) {n : ℕ}
    (h : NearestMagnitude q n) : |q - n| ≤ |q - ⌊q⌋| ∧ |q - n| ≤ |q - (⌊q⌋ + 1)| := by
  have hf : ((⌊q⌋₊ : ℕ) : K) = (⌊q⌋ : K) := by exact_mod_cast Int.natCast_floor_eq_floor hq
  constructor
  · have := h ⌊q⌋₊
    rwa [hf] at this
  · have := h (⌊q⌋₊ + 1)
    push_cast at this
    rwa [hf] at this

theorem roundInt_of_mantissaRounds_positive (mode : RoundingMode) {q : K} (hq : 0 ≤ q) {n : ℕ}
    (h : MantissaRounds mode .positive q n) : roundInt mode q = n := by
  have hx := Int.floor_add_fract q
  have hfr0 := Int.fract_nonneg q
  have hfr1 := Int.fract_lt_one q
  -- Nearest directions: `n` is the floor or the next integer.
  have near : NearestMagnitude q n →
      (Int.fract q < 1 / 2 → (n : ℤ) = ⌊q⌋) ∧ (1 / 2 < Int.fract q → (n : ℤ) = ⌊q⌋ + 1) ∧
        (Int.fract q = 1 / 2 → (n : ℤ) = ⌊q⌋ ∨ (n : ℤ) = ⌊q⌋ + 1) := by
    intro hn
    obtain ⟨h1, h2⟩ := abs_sub_le_half_of_nearest hq hn
    have hd1 : |q - ⌊q⌋| = Int.fract q := by
      rw [Int.self_sub_floor, abs_of_nonneg hfr0]
    have hd2 : |q - (⌊q⌋ + 1)| = 1 - Int.fract q := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    rw [hd1] at h1
    rw [hd2] at h2
    have hlo := neg_abs_le (q - n)
    have hhi := le_abs_self (q - n)
    refine ⟨fun hlt => ?_, fun hgt => ?_, fun heq => ?_⟩
    · have a1 : (n : K) < ⌊q⌋ + 1 := by linarith
      have a2 : (⌊q⌋ : K) < n + 1 := by linarith
      have b1 : (n : ℤ) < ⌊q⌋ + 1 := by exact_mod_cast a1
      have b2 : ⌊q⌋ < (n : ℤ) + 1 := by exact_mod_cast a2
      omega
    · have a1 : (n : K) < ⌊q⌋ + 2 := by linarith
      have a2 : (⌊q⌋ : K) < n := by linarith
      have b1 : (n : ℤ) < ⌊q⌋ + 2 := by exact_mod_cast a1
      have b2 : ⌊q⌋ < (n : ℤ) := by exact_mod_cast a2
      omega
    · have a1 : (n : K) ≤ ⌊q⌋ + 1 := by linarith
      have a2 : (⌊q⌋ : K) ≤ n := by linarith
      have b1 : (n : ℤ) ≤ ⌊q⌋ + 1 := by exact_mod_cast a1
      have b2 : ⌊q⌋ ≤ (n : ℤ) := by exact_mod_cast a2
      omega
  have hfNat : ((⌊q⌋₊ : ℕ) : ℤ) = ⌊q⌋ := Int.natCast_floor_eq_floor hq
  cases mode with
  | towardZero =>
    simp only [MantissaRounds] at h
    simp [roundInt, hq, floor_eq_of_lower h]
  | towardNegative =>
    simp only [MantissaRounds, reduceCtorEq, ↓reduceIte] at h
    simp [roundInt, floor_eq_of_lower h]
  | towardPositive =>
    simp only [MantissaRounds, ↓reduceIte] at h
    simp [roundInt, ceil_eq_of_upper hq h]
  | nearestTiesToEven =>
    obtain ⟨hn, htie⟩ := h
    obtain ⟨n1, n2, n3⟩ := near hn
    rcases lt_trichotomy (Int.fract q) (1 / 2) with hlt | heq | hgt
    · rw [roundInt_nearest_of_fract_lt (Or.inl rfl) hlt, n1 hlt]
    · have e1 : ¬ Int.fract q < 1 / 2 := by linarith
      have e2 : ¬ 1 / 2 < Int.fract q := by linarith
      simp only [roundInt, e1, e2, ↓reduceIte]
      -- Both neighbours are at distance one half.
      have hdist : |q - ⌊q⌋₊| = |q - (⌊q⌋₊ + 1 : ℕ)| := by
        have hf : ((⌊q⌋₊ : ℕ) : K) = (⌊q⌋ : K) := by exact_mod_cast hfNat
        push_cast
        rw [hf, show q - (⌊q⌋ : K) = 1 / 2 by linarith,
          show q - ((⌊q⌋ : K) + 1) = -(1 / 2) by linarith]
        norm_num
      rcases n3 heq with hn' | hn'
      · -- `n` is the floor, so it must be even or the only choice.
        have hnat : n = ⌊q⌋₊ := by omega
        subst hnat
        have := htie (⌊q⌋₊ + 1) hdist
        split_ifs with hev
        · omega
        · omega
      · have hnat : n = ⌊q⌋₊ + 1 := by omega
        subst hnat
        have := htie ⌊q⌋₊ hdist.symm
        split_ifs with hev
        · omega
        · omega
    · rw [roundInt_nearest_of_lt_fract (Or.inl rfl) hgt, n2 hgt]
  | nearestTiesToAway =>
    obtain ⟨hn, htie⟩ := h
    obtain ⟨n1, n2, n3⟩ := near hn
    rcases lt_trichotomy (Int.fract q) (1 / 2) with hlt | heq | hgt
    · rw [roundInt_nearest_of_fract_lt (Or.inr rfl) hlt, n1 hlt]
    · have e1 : ¬ Int.fract q < 1 / 2 := by linarith
      have e2 : ¬ 1 / 2 < Int.fract q := by linarith
      simp only [roundInt, e1, e2, hq, ↓reduceIte]
      have hdist : |q - n| = |q - (⌊q⌋₊ + 1 : ℕ)| := by
        have hf : ((⌊q⌋₊ : ℕ) : K) = (⌊q⌋ : K) := by exact_mod_cast hfNat
        rcases n3 heq with hn' | hn'
        · have hnq : (n : K) = ⌊q⌋ := by exact_mod_cast hn'
          push_cast
          rw [hf, hnq, show q - (⌊q⌋ : K) = 1 / 2 by linarith,
            show q - ((⌊q⌋ : K) + 1) = -(1 / 2) by linarith]
          norm_num
        · have hnq : (n : K) = ⌊q⌋ + 1 := by exact_mod_cast hn'
          push_cast
          rw [hf, hnq]
      have := htie (⌊q⌋₊ + 1) hdist
      rcases n3 heq with hn' | hn' <;> omega
    · rw [roundInt_nearest_of_lt_fract (Or.inr rfl) hgt, n2 hgt]

omit [IsStrictOrderedRing K] [FloorRing K] in
theorem mantissaRounds_negative (mode : RoundingMode) (q : K) (n : ℕ) :
    MantissaRounds mode .negative q n ↔ MantissaRounds (reflectMode mode) .positive q n := by
  cases mode <;> simp [MantissaRounds, reflectMode]

/-- The significand certificate of the executable rounding selects exactly the
integer chosen by `roundInt` for the signed magnitude. -/
theorem roundInt_of_mantissaRounds (mode : RoundingMode) (sign : Sign) {q : K} (hq : 0 ≤ q)
    {n : ℕ} (h : MantissaRounds mode sign q n) :
    roundInt mode (if sign = .negative then -q else q) = sign.apply n := by
  cases sign with
  | positive =>
    simp only [reduceCtorEq, ↓reduceIte, Sign.apply]
    exact roundInt_of_mantissaRounds_positive mode hq h
  | negative =>
    simp only [↓reduceIte, Sign.apply]
    rw [roundInt_neg, roundInt_of_mantissaRounds_positive (reflectMode mode) hq
      ((mantissaRounds_negative mode q n).mp h)]

end Mantissa

/-! ## The executable grid is the specification's grid -/

section Grid

theorem leadingExponent_dyadic (sign : Sign) {n : ℕ} (hn : 0 < n) (e : ℤ) :
    leadingExponent (dyadic (sign.apply n) e) = n.log2 + e := by
  apply leadingExponent_eq
  · rw [abs_dyadic_sign, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hn))
      (two_zpow_pos e).le
  · rw [abs_dyadic_sign, show (n.log2 : ℤ) + e + 1 = ((n.log2 + 1 : ℕ) : ℤ) + e by push_cast; ring,
      zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_log2_self) (two_zpow_pos e)

/-- The executable's target exponent is the specification's grid exponent. -/
theorem quantum_dyadic (f : Format) (sign : Sign) {n : ℕ} (hn : 0 < n) (e : ℤ) :
    quantum f (dyadic (sign.apply n) e) = f.targetExponent (totalExponent n e) := by
  rw [quantum, leadingExponent_dyadic sign hn e]
  have hmin := minQuantum_eq_minExponent f
  unfold minQuantum at hmin
  unfold Format.targetExponent totalExponent precision at *
  omega

/-- The executable rounding of a finite unpacked value has the value
`roundGradual` of its exact value. -/
theorem value?_roundUnpacked_finite (f : Format) (mode : RoundingMode) (sign : Sign) {n : ℕ}
    (hn : 0 < n) (e : ℤ) :
    value? (Rounding.roundUnpacked f mode (.finite sign n e hn)) =
      some (roundGradual f mode (dyadic (sign.apply n) e)) := by
  obtain ⟨m, hm, hv⟩ := roundUnpacked_finite_correct f mode sign n e hn
  rw [hv]
  congr 1
  unfold roundGradual roundAt
  rw [quantum_dyadic f sign hn e]
  set T := f.targetExponent (totalExponent n e)
  have hq : 0 ≤ (n : ℚ) * 2 ^ e / 2 ^ T := by positivity
  have hsplit : dyadic (sign.apply n) e / 2 ^ T =
      if sign = .negative then -((n : ℚ) * 2 ^ e / 2 ^ T) else (n : ℚ) * 2 ^ e / 2 ^ T := by
    cases sign <;> simp [dyadic, Sign.apply, neg_div]
  rw [hsplit, roundInt_of_mantissaRounds mode sign hq hm]
  rfl

theorem value?_roundUnpacked (f : Format) (mode : RoundingMode) {u : UnpackedFloat} {v : ℚ}
    (hv : value? u = some v) :
    value? (Rounding.roundUnpacked f mode u) = some (roundGradual f mode v) := by
  cases u with
  | notANumber => simp [value?] at hv
  | infinity sign => simp [value?] at hv
  | zero sign =>
    have : v = 0 := by simpa [value?] using hv.symm
    subst this
    simp [Rounding.roundUnpacked, value?]
  | finite sign n e hn =>
    simp only [value?, Option.some.injEq] at hv
    subst hv
    exact value?_roundUnpacked_finite f mode sign hn e

end Grid

/-! ## Overflow of the executable result -/

section Overflow

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- No overflow occurs exactly when the finite rounded value is at most the
largest finite magnitude. -/
theorem abs_roundGradual_le_iff (f : Format) (mode : RoundingMode) (x : K) :
    |roundGradual f mode x| ≤ maxFinite f ↔ ¬ Overflows f mode x := by
  unfold Overflows
  rw [not_lt]
  by_cases hle : emin f ≤ leadingExponent x
  · have heq : quantum f x = unboundedQuantum f x := by
      unfold quantum unboundedQuantum
      omega
    unfold roundGradual roundUnbounded
    rw [heq]
  · -- Below the normal range both roundings stay within `2 ^ emin`.
    have hx : x ≠ 0 := by
      intro h0
      apply hle
      subst h0
      have := one_le_emax f
      simp [leadingExponent, emin]
      omega
    have hsmall : |x| ≤ (2 : K) ^ emin f := by
      have := abs_lt_two_zpow_leadingExponent x
      exact le_trans this.le (zpow_le_zpow_right₀ (by norm_num) (by omega))
    have hmin := two_zpow_emin_le_maxFinite (K := K) f
    have bound : ∀ q : ℤ, q ≤ emin f → |roundAt mode q x| ≤ maxFinite f := by
      intro q hq
      obtain ⟨m, hm⟩ := intMul_of_le (K := K) hq 1
      simp only [Int.cast_one, one_mul] at hm
      have := abs_roundAt_le mode q m (by rw [← hm]; exact hsmall)
      rw [← hm] at this
      exact le_trans this hmin
    have hp := two_le_precision f
    constructor
    · intro _
      exact bound _ (by unfold unboundedQuantum; omega)
    · intro _
      exact bound _ (by unfold quantum; omega)

/-- For a canonical finite value, the encoder's exponent-range test is the
bound by the largest finite magnitude. -/
theorem noExponentOverflow_iff (f : Format) (sign : Sign) {m : ℕ} {E : ℤ} (hm : 0 < m)
    (hnorm : ExponentNormalized f (.finite sign m E hm)) :
    NoExponentOverflow f (.finite sign m E hm) ↔ |dyadic (sign.apply m) E| ≤ maxFinite f := by
  obtain ⟨hEmin, hmlt, hcase⟩ := ExponentNormalized.finite_bounds f sign m E hm hnorm
  have hbias := emax_eq f
  have hw := f.he
  have hpowNat : 2 ^ f.exponentBits = 2 * 2 ^ (f.exponentBits - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 1 ≤ 2 ^ (f.exponentBits - 1) := Nat.one_le_two_pow
  have hminE : f.minExponent = minQuantum f := (minQuantum_eq_minExponent f).symm
  have hmq : minQuantum f ≤ maxQuantum f := by
    have := emin_le_emax f
    unfold minQuantum maxQuantum
    omega
  have hmaxq : maxQuantum f = (f.exponentBias : ℤ) - f.mantissaBitsWithoutImplicit := by
    unfold maxQuantum precision emax Format.mantissaBits
    push_cast
    ring
  have hBias : ((f.exponentBias : ℕ) : ℤ) = (2 : ℤ) ^ (f.exponentBits - 1) - 1 := hbias
  have hlow : 0 ≤ E + f.exponentBias + f.mantissaBitsWithoutImplicit := by
    have : minQuantum f = 1 - ((f.exponentBias : ℕ) : ℤ) - f.mantissaBitsWithoutImplicit := by
      unfold minQuantum emin precision emax Format.mantissaBits
      push_cast
      ring
    omega
  have hrange : NoExponentOverflow f (.finite sign m E hm) ↔ E ≤ maxQuantum f := by
    change (E + f.exponentBias + f.mantissaBitsWithoutImplicit).toNat < 2 ^ f.exponentBits - 1 ↔ _
    have hc : ((2 ^ f.exponentBits - 1 : ℕ) : ℤ) = 2 * (2 : ℤ) ^ (f.exponentBits - 1) - 1 := by
      rw [hpowNat, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hmaxq]
    constructor
    · intro h
      have h' : ((E + f.exponentBias + f.mantissaBitsWithoutImplicit).toNat : ℤ) <
          ((2 ^ f.exponentBits - 1 : ℕ) : ℤ) := by exact_mod_cast h
      rw [Int.toNat_of_nonneg hlow, hc] at h'
      omega
    · intro h
      have : ((E + f.exponentBias + f.mantissaBitsWithoutImplicit).toNat : ℤ) <
          ((2 ^ f.exponentBits - 1 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hlow, hc]
        omega
      exact_mod_cast this
  rw [hrange, abs_dyadic_sign]
  constructor
  · intro hE
    unfold maxFinite maxSignificand
    apply mul_le_mul _ (zpow_le_zpow_right₀ (by norm_num) hE) (two_zpow_pos E).le (by
      have := maxSignificand_pos f
      unfold maxSignificand at this
      exact_mod_cast this.le)
    have : (m : ℤ) ≤ 2 ^ f.mantissaBits - 1 := by
      have : (m : ℤ) < 2 ^ f.mantissaBits := by exact_mod_cast hmlt
      omega
    exact_mod_cast this
  · intro hle
    by_contra hE'
    have hE : maxQuantum f < E := lt_of_not_ge hE'
    have hne : E ≠ f.minExponent := by omega
    have hbig : 2 ^ (f.mantissaBits - 1) ≤ m := hcase.resolve_left hne
    have hpm : 1 ≤ f.mantissaBits := by unfold Format.mantissaBits; omega
    have h1 : (2 : ℚ) ^ (emax f + 1) ≤ (m : ℚ) * 2 ^ E := by
      have hsplit : (2 : ℚ) ^ (emax f + 1) = 2 ^ ((f.mantissaBits - 1 : ℕ) : ℤ) *
          2 ^ (maxQuantum f + 1) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1
        unfold maxQuantum precision
        push_cast [Nat.cast_sub hpm]
        ring
      rw [hsplit, zpow_natCast]
      apply mul_le_mul (by exact_mod_cast hbig) (zpow_le_zpow_right₀ (by norm_num) (by omega))
        (two_zpow_pos _).le (by positivity)
    have := maxFinite_lt (K := ℚ) f
    linarith

end Overflow

/-! ## The executable result is the delivered result -/

/-- The delivered result denoted by an unpacked value; a NaN denotes none. -/
def roundedOf? : UnpackedFloat → Option (Rounded ℚ)
  | .zero _ => some (.finite 0)
  | .finite sign mantissa exponent _ => some (.finite (dyadic (sign.apply mantissa) exponent))
  | .infinity sign => some (.infinite (decide (sign = .negative)))
  | .notANumber => none

theorem roundedOf?_eq_finite_iff (u : UnpackedFloat) (v : ℚ) :
    roundedOf? u = some (.finite v) ↔ value? u = some v := by
  cases u <;> simp [roundedOf?, value?, eq_comm]

private theorem overflowToInfinity_eq (mode : RoundingMode) (sign : Sign) :
    Rounding.overflowToInfinity mode sign = overflowsToInfinity mode (decide (sign = .negative)) := by
  cases mode <;> cases sign <;> rfl

/-- The value of the saturation encoding is the largest finite number. -/
theorem value?_largestFinite (f : Format) (sign : Sign) :
    value? (largestFinite f sign) =
      some (if sign = .negative then -maxFinite f else maxFinite f) := by
  have hw := f.he
  have hpowNat : 2 ^ f.exponentBits = 2 * 2 ^ (f.exponentBits - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 1 ≤ 2 ^ (f.exponentBits - 1) := Nat.one_le_two_pow
  have hexp : ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) - (f.exponentBias : ℤ) -
      f.mantissaBitsWithoutImplicit = maxQuantum f := by
    have hb := emax_eq f
    unfold maxQuantum precision emax Format.mantissaBits at *
    rw [Nat.cast_sub (by omega)]
    push_cast [hpowNat]
    omega
  have hsig : ((2 ^ f.mantissaBits - 1 : ℕ) : ℤ) = maxSignificand f := by
    unfold maxSignificand
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    rfl
  simp only [largestFinite, value?, Option.some.injEq]
  rw [hexp]
  cases sign <;> simp [dyadic, Sign.apply, maxFinite, hsig]

theorem value_nonneg_iff (sign : Sign) {n : ℕ} (hn : 0 < n) (e : ℤ) :
    dyadic (sign.apply n) e < 0 ↔ sign = .negative := by
  have h2 := two_zpow_pos (K := ℚ) e
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  cases sign <;> simp [dyadic, Sign.apply] <;> positivity

/-- The executable packed rounding delivers exactly `deliver` of the exact
value, including the overflow result, for every finite unpacked input. -/
theorem roundedOf?_unpack_packRounded (f : Format) (mode : RoundingMode) {u : UnpackedFloat}
    {v : ℚ} (hv : value? u = some v) :
    roundedOf? (UnpackedFloat.unpack f (Rounding.packRounded f mode u)) = some (deliver f mode v) := by
  have hr := value?_roundUnpacked f mode hv
  have hnorm := roundUnpacked_normalized f mode u
  by_cases ho : Overflows f mode v
  · have hbig : maxFinite f < |roundGradual f mode v| :=
      lt_of_not_ge fun h => ((abs_roundGradual_le_iff f mode v).mp h) ho
    cases u with
    | notANumber => simp [value?] at hv
    | infinity sign => simp [value?] at hv
    | zero sign =>
      have : v = 0 := by simpa [value?] using hv.symm
      subst this
      exact absurd ho (not_overflows_of_abs_le f mode (by simp [(maxFinite_pos f).le]))
    | finite sign n e hn =>
      simp only [value?, Option.some.injEq] at hv
      subst hv
      have hsign : ∀ s' m E hm, Rounding.roundUnpacked f mode (.finite sign n e hn) =
          .finite s' m E hm → s' = sign := by
        intro s' m E hm h
        simp only [Rounding.roundUnpacked, Rounding.roundWithAccuracy] at h
        split at h
        · cases h
        · cases h
          rfl
      generalize hru : Rounding.roundUnpacked f mode (.finite sign n e hn) = r at hr hnorm hsign
      cases r with
      | notANumber => simp [value?] at hr
      | infinity s' => simp [value?] at hr
      | zero s' =>
        simp only [value?, Option.some.injEq] at hr
        rw [← hr] at hbig
        simp only [abs_zero] at hbig
        exact absurd hbig (not_lt.mpr (maxFinite_pos f).le)
      | finite s' m E hm =>
        obtain rfl := hsign s' m E hm rfl
        simp only [value?, Option.some.injEq] at hr
        have hover : ¬ NoExponentOverflow f (.finite s' m E hm) := by
          rw [noExponentOverflow_iff f s' hm hnorm, hr]
          exact not_le.mpr hbig
        have hover' : 2 ^ f.exponentBits ≤
            (E + f.exponentBias + f.mantissaBitsWithoutImplicit).toNat + 1 := by
          change ¬ ((E + f.exponentBias + f.mantissaBitsWithoutImplicit).toNat <
            2 ^ f.exponentBits - 1) at hover
          omega
        have hpack : Rounding.packRounded f mode (.finite s' n e hn) =
            Rounding.packNormalized f mode (.finite s' m E hm) := by
          unfold Rounding.packRounded
          rw [hru]
        rw [hpack, unpack_packNormalized_overflow f mode s' m E hm hover']
        have hneg := value_nonneg_iff s' hn e
        unfold deliver
        simp only [ho, ↓reduceIte, overflowToInfinity_eq, decide_eq_decide.mpr hneg]
        split
        · simp [roundedOf?]
        · have hl := value?_largestFinite f s'
          cases hlf : largestFinite f s' with
          | finite s'' m' e' hm' =>
            rw [hlf] at hl
            simp only [roundedOf?, value?, Option.some.injEq] at hl ⊢
            rw [hl]
            simp only [hneg]
          | _ => simp [largestFinite] at hlf
  · have hle := (abs_roundGradual_le_iff f mode v).mpr ho
    have hin : NoExponentOverflow f (Rounding.roundUnpacked f mode u) := by
      generalize hru : Rounding.roundUnpacked f mode u = r at hr hnorm
      cases r with
      | finite sign m E hm =>
        rw [noExponentOverflow_iff f sign hm hnorm]
        simp only [value?, Option.some.injEq] at hr
        rw [hr]
        exact hle
      | _ => trivial
    rw [unpack_packRounded f mode u hin, deliver_of_not_overflows ho,
      roundedOf?_eq_finite_iff]
    exact hr

/-! ## Integral rounding -/

/-- The executable unbounded integer rounding is `roundInt` of the exact value,
and fails exactly for NaN and infinities. -/
theorem toInt?_eq_roundInt (mode : RoundingMode) (u : UnpackedFloat) :
    Rounding.toInt? mode u = (value? u).map (roundInt mode) := by
  cases u with
  | notANumber => rfl
  | infinity s => rfl
  | zero s => simp [Rounding.toInt?, value?]
  | finite sign n e hn =>
    obtain ⟨rounded, hr, hm⟩ := toInt?_finite_correct mode sign n e hn
    rw [hr]
    have hq : (0 : ℚ) ≤ (n : ℚ) * 2 ^ e := by positivity
    have := roundInt_of_mantissaRounds mode sign hq hm
    simp only [value?, Option.map_some, Option.some.injEq]
    rw [← this]
    congr 1
    cases sign <;> simp [dyadic, Sign.apply]

/-- The executable integral rounding (`Rounding.integralRounded`, which rounds
`ROUNDSS`, WebAssembly `ceil`/`floor`/`trunc`/`nearest`, …) delivers `deliver`
of the integer `roundInt mode v` for every finite input of value `v`. -/
theorem roundedOf?_unpack_integralRounded (f : Format) (mode : RoundingMode)
    {u : UnpackedFloat} {v : ℚ} (hv : value? u = some v) :
    roundedOf? (UnpackedFloat.unpack f (Rounding.integralRounded f mode u)) =
      some (deliver f mode ((roundInt mode v : ℤ) : ℚ)) := by
  cases u with
  | notANumber => simp [value?] at hv
  | infinity s => simp [value?] at hv
  | zero s =>
    have : v = 0 := by simpa [value?] using hv.symm
    subst this
    simp only [Rounding.integralRounded, roundInt_zero, Int.cast_zero]
    exact roundedOf?_unpack_packRounded f mode hv
  | finite sign n e hn =>
    have ht := toInt?_eq_roundInt mode (.finite sign n e hn)
    rw [hv, Option.map_some] at ht
    simp only [Rounding.integralRounded, ht]
    exact roundedOf?_unpack_packRounded f mode (by simp [dyadic])

/-- Rounding a finite value of a format to an integer gives a finite value of
the format, provided every integer up to `2 ^ (p - 1)` is one (`0 ≤ maxQuantum`,
true of binary16, bfloat16, binary32 and binary64). Without that proviso a
format with a narrow exponent range can overflow on rounding to integral. -/
theorem representable_roundInt {f : Format} (h0 : 0 ≤ maxQuantum f) (mode : RoundingMode)
    {v : ℚ} (h : Representable f v) : Representable f ((roundInt mode v : ℤ) : ℚ) := by
  obtain ⟨n, q, hv, hn, hq, hmax⟩ := h
  by_cases hq0 : 0 ≤ q
  · have hint : v = ((n * 2 ^ q.toNat : ℤ) : ℚ) := by
      rw [hv]; push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg hq0]
    rw [hint, roundInt_intCast, ← hint]
    exact ⟨n, q, hv, hn, hq, hmax⟩
  · have hp := two_le_precision f
    set M : ℤ := 2 ^ (f.mantissaBits - 1) with hM
    have hMp : 2 * M = 2 ^ f.mantissaBits := by
      rw [hM, ← pow_succ']
      congr 1
      unfold precision at hp
      omega
    have hq1 : (2 : ℚ) ^ q ≤ 1 / 2 := by
      rw [show (1 / 2 : ℚ) = 2 ^ (-1 : ℤ) by norm_num]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hn' : ((|n| : ℤ) : ℚ) ≤ 2 * M - 1 := by
      have : |n| ≤ 2 * M - 1 := by omega
      exact_mod_cast this
    have hv' : |v| ≤ (M : ℚ) := by
      rw [hv, abs_mul, abs_of_pos (two_zpow_pos (K := ℚ) q), ← Int.cast_abs]
      have hM0 : (0 : ℚ) ≤ 2 * M - 1 := by
        have : (1 : ℤ) ≤ M := by rw [hM]; exact one_le_pow₀ (by norm_num)
        have : (1 : ℚ) ≤ M := by exact_mod_cast this
        linarith
      calc ((|n| : ℤ) : ℚ) * 2 ^ q ≤ (2 * M - 1) * (1 / 2) :=
            mul_le_mul hn' hq1 (two_zpow_pos q).le hM0
        _ ≤ M := by linarith
    have hup : roundInt mode v ≤ M := by
      have := roundInt_mono mode (le_trans (le_abs_self v) hv')
      rwa [show ((M : ℤ) : ℚ) = (M : ℚ) from rfl, roundInt_intCast] at this
    have hlo : -M ≤ roundInt mode v := by
      have hle : ((-M : ℤ) : ℚ) ≤ v := by
        push_cast
        linarith [neg_abs_le v]
      have := roundInt_mono mode hle
      rwa [roundInt_intCast] at this
    have hk : |roundInt mode v| < 2 ^ f.mantissaBits := by
      rw [← hMp]
      have : (1 : ℤ) ≤ M := by rw [hM]; exact one_le_pow₀ (by norm_num)
      rw [abs_lt]
      constructor <;> omega
    have := representable_of_significand f hk (q := 0)
      (by rw [minQuantum_eq_minExponent]; unfold Format.minExponent Format.mantissaBits
          have : (2 : ℤ) ≤ 2 ^ (f.exponentBits - 1) := by
            have he := f.he
            calc (2 : ℤ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (f.exponentBits - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          push_cast
          omega)
      h0
    simpa using this

end Silmaril.Numeric.Ieee754.FlagSpec

/-! ## Binary32 and binary64 values agree with the delivered results -/

namespace Silmaril.Numeric.Ieee754

open Float.Model Float.Model.UnpackedFloat Conformance FlagSpec

namespace F32

/-- The delivered result denoted by a raw binary32 encoding; a NaN denotes none. -/
def rounded? (x : F32) : Option (Rounded ℚ) :=
  roundedOf? (UnpackedFloat.unpack .binary32 x.bits.toBitVec)

theorem toRat?_eq_iff_rounded? (x : F32) (v : ℚ) : x.toRat? = some v ↔ x.rounded? = some (.finite v) := by
  rw [rounded?, roundedOf?_eq_finite_iff, F32.value?_unpack_bits]

theorem addWith_rounded? (mode : RoundingMode) {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (addWith mode x y).rounded? = some (deliver .binary32 mode (a + b)) :=
  roundedOf?_unpack_packRounded .binary32 mode (value?_addExact mode
    ((value?_model_unpack32 x).trans hx) ((value?_model_unpack32 y).trans hy))

theorem subWith_rounded? (mode : RoundingMode) {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (subWith mode x y).rounded? = some (deliver .binary32 mode (a - b)) :=
  roundedOf?_unpack_packRounded .binary32 mode (value?_subExact mode
    ((value?_model_unpack32 x).trans hx) ((value?_model_unpack32 y).trans hy))

theorem mulWith_rounded? (mode : RoundingMode) {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (mulWith mode x y).rounded? = some (deliver .binary32 mode (a * b)) :=
  roundedOf?_unpack_packRounded .binary32 mode (value?_mulExact
    ((value?_model_unpack32 x).trans hx) ((value?_model_unpack32 y).trans hy))

theorem fmaWith_rounded? (mode : RoundingMode) {x y z : F32} {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c) :
    (fmaWith mode x y z).rounded? = some (deliver .binary32 mode (a * b + c)) :=
  roundedOf?_unpack_packRounded .binary32 mode (value?_fmaExact mode
    ((value?_model_unpack32 x).trans hx) ((value?_model_unpack32 y).trans hy)
    ((value?_model_unpack32 z).trans hz))

theorem ofInt_rounded? (mode : RoundingMode) (n : ℤ) :
    (F32.ofInt n mode).rounded? = some (deliver .binary32 mode (n : ℚ)) :=
  roundedOf?_unpack_packRounded .binary32 mode (value?_ofInt n)

/-- The inexact flag of addition holds exactly when the value returned by
`addWith` differs from the exact sum (IEEE 754-2019 §7.6). -/
theorem addFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (x.addFlags mode tininess y).inexact = true ↔ (addWith mode x y).toRat? ≠ some (a + b) := by
  obtain ⟨nx, hdx⟩ := (F32.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F32.toRat?_eq_some_iff y b).mp hy
  rw [addFlags, hdx, hdy, add_finite, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, addWith_rounded? mode hx hy, Option.some.injEq]

theorem subFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (x.subFlags mode tininess y).inexact = true ↔ (subWith mode x y).toRat? ≠ some (a - b) := by
  obtain ⟨nx, hdx⟩ := (F32.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F32.toRat?_eq_some_iff y b).mp hy
  rw [subFlags, hdx, hdy, sub_finite, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, subWith_rounded? mode hx hy, Option.some.injEq]

theorem mulFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (x.mulFlags mode tininess y).inexact = true ↔ (mulWith mode x y).toRat? ≠ some (a * b) := by
  obtain ⟨nx, hdx⟩ := (F32.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F32.toRat?_eq_some_iff y b).mp hy
  rw [mulFlags, hdx, hdy, mul_finite, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, mulWith_rounded? mode hx hy, Option.some.injEq]

theorem fmaFlags_inexact_iff (policy : FmaQuietAddend) (mode : RoundingMode) (tininess : Tininess)
    {x y z : F32} {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c) :
    (fmaFlags policy mode tininess x y z).inexact = true ↔
      (fmaWith mode x y z).toRat? ≠ some (a * b + c) := by
  obtain ⟨nx, hdx⟩ := (F32.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F32.toRat?_eq_some_iff y b).mp hy
  obtain ⟨nz, hdz⟩ := (F32.toRat?_eq_some_iff z c).mp hz
  rw [fmaFlags, hdx, hdy, hdz, fma_finite, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, fmaWith_rounded? mode hx hy hz, Option.some.injEq]

theorem ofIntFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) (n : ℤ) :
    (F32.ofIntFlags mode tininess n).inexact = true ↔ (F32.ofInt n mode).toRat? ≠ some (n : ℚ) := by
  rw [ofIntFlags, FlagSpec.ofInt, roundingFlags_inexact, ne_eq, ne_eq, toRat?_eq_iff_rounded?,
    ofInt_rounded? mode n, Option.some.injEq]

/-- Integral rounding of a finite operand returns the integer `roundInt mode a`
exactly. -/
theorem roundIntegral_rounded? (mode : RoundingMode) {x : F32} {a : ℚ} (hx : x.toRat? = some a) :
    (roundIntegral mode x).rounded? = some (.finite ((roundInt mode a : ℤ) : ℚ)) := by
  obtain ⟨n, hd⟩ := (F32.toRat?_eq_some_iff x a).mp hx
  have hrep := representable_roundInt (by decide +kernel) mode (F32.datum_finite_representable x hd)
  rw [rounded?, show (roundIntegral mode x).bits.toBitVec =
    Rounding.integralRounded .binary32 mode x.model.unpack from rfl,
    roundedOf?_unpack_integralRounded .binary32 mode ((value?_model_unpack32 x).trans hx),
    deliver_of_representable _ _ hrep]

/-- The inexact flag of `roundToIntegralExact` holds exactly when the value
returned by `roundIntegral` differs from the operand (IEEE 754-2019 §5.9). -/
theorem roundToIntegralFlags_inexact_iff (mode : RoundingMode) {x : F32} {a : ℚ}
    (hx : x.toRat? = some a) :
    (FlagSpec.roundToIntegral mode true x.datum).inexact = true ↔
      (roundIntegral mode x).toRat? ≠ some a := by
  obtain ⟨n, hd⟩ := (F32.toRat?_eq_some_iff x a).mp hx
  rw [hd, ne_eq, toRat?_eq_iff_rounded?, roundIntegral_rounded? mode hx]
  simp only [FlagSpec.roundToIntegral, Bool.true_and, ne_eq, Option.some.injEq]
  by_cases h : ((roundInt mode a : ℤ) : ℚ) = a <;> simp [h, inexactOnly, Flags.singleton, Flags.ofFunction]

end F32

namespace F64

/-- The delivered result denoted by a raw binary64 encoding; a NaN denotes none. -/
def rounded? (x : F64) : Option (Rounded ℚ) :=
  roundedOf? (UnpackedFloat.unpack .binary64 x.bits.toBitVec)

theorem toRat?_eq_iff_rounded? (x : F64) (v : ℚ) : x.toRat? = some v ↔ x.rounded? = some (.finite v) := by
  rw [rounded?, roundedOf?_eq_finite_iff, F64.value?_unpack_bits]

theorem addWith_rounded? (mode : RoundingMode) {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (addWith mode x y).rounded? = some (deliver .binary64 mode (a + b)) :=
  roundedOf?_unpack_packRounded .binary64 mode (value?_addExact mode
    ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy))

theorem subWith_rounded? (mode : RoundingMode) {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (subWith mode x y).rounded? = some (deliver .binary64 mode (a - b)) :=
  roundedOf?_unpack_packRounded .binary64 mode (value?_subExact mode
    ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy))

theorem mulWith_rounded? (mode : RoundingMode) {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (mulWith mode x y).rounded? = some (deliver .binary64 mode (a * b)) :=
  roundedOf?_unpack_packRounded .binary64 mode (value?_mulExact
    ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy))

theorem fmaWith_rounded? (mode : RoundingMode) {x y z : F64} {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c) :
    (fmaWith mode x y z).rounded? = some (deliver .binary64 mode (a * b + c)) :=
  roundedOf?_unpack_packRounded .binary64 mode (value?_fmaExact mode
    ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy)
    ((value?_model_unpack64 z).trans hz))

theorem ofInt_rounded? (mode : RoundingMode) (n : ℤ) :
    (F64.ofInt n mode).rounded? = some (deliver .binary64 mode (n : ℚ)) :=
  roundedOf?_unpack_packRounded .binary64 mode (value?_ofInt n)

/-- The inexact flag of addition holds exactly when the value returned by
`addWith` differs from the exact sum (IEEE 754-2019 §7.6). -/
theorem addFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (x.addFlags mode tininess y).inexact = true ↔ (addWith mode x y).toRat? ≠ some (a + b) := by
  obtain ⟨nx, hdx⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F64.toRat?_eq_some_iff y b).mp hy
  rw [addFlags, hdx, hdy, add_finite, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, addWith_rounded? mode hx hy, Option.some.injEq]

theorem subFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (x.subFlags mode tininess y).inexact = true ↔ (subWith mode x y).toRat? ≠ some (a - b) := by
  obtain ⟨nx, hdx⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F64.toRat?_eq_some_iff y b).mp hy
  rw [subFlags, hdx, hdy, sub_finite, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, subWith_rounded? mode hx hy, Option.some.injEq]

theorem mulFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (x.mulFlags mode tininess y).inexact = true ↔ (mulWith mode x y).toRat? ≠ some (a * b) := by
  obtain ⟨nx, hdx⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F64.toRat?_eq_some_iff y b).mp hy
  rw [mulFlags, hdx, hdy, mul_finite, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, mulWith_rounded? mode hx hy, Option.some.injEq]

theorem fmaFlags_inexact_iff (policy : FmaQuietAddend) (mode : RoundingMode) (tininess : Tininess)
    {x y z : F64} {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c) :
    (fmaFlags policy mode tininess x y z).inexact = true ↔
      (fmaWith mode x y z).toRat? ≠ some (a * b + c) := by
  obtain ⟨nx, hdx⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F64.toRat?_eq_some_iff y b).mp hy
  obtain ⟨nz, hdz⟩ := (F64.toRat?_eq_some_iff z c).mp hz
  rw [fmaFlags, hdx, hdy, hdz, fma_finite, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, fmaWith_rounded? mode hx hy hz, Option.some.injEq]

theorem ofIntFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) (n : ℤ) :
    (F64.ofIntFlags mode tininess n).inexact = true ↔ (F64.ofInt n mode).toRat? ≠ some (n : ℚ) := by
  rw [ofIntFlags, FlagSpec.ofInt, roundingFlags_inexact, ne_eq, ne_eq, toRat?_eq_iff_rounded?,
    ofInt_rounded? mode n, Option.some.injEq]

/-- Integral rounding of a finite operand returns the integer `roundInt mode a`
exactly. -/
theorem roundIntegral_rounded? (mode : RoundingMode) {x : F64} {a : ℚ} (hx : x.toRat? = some a) :
    (roundIntegral mode x).rounded? = some (.finite ((roundInt mode a : ℤ) : ℚ)) := by
  obtain ⟨n, hd⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  have hrep := representable_roundInt (by decide +kernel) mode (F64.datum_finite_representable x hd)
  rw [rounded?, show (roundIntegral mode x).bits.toBitVec =
    Rounding.integralRounded .binary64 mode x.model.unpack from rfl,
    roundedOf?_unpack_integralRounded .binary64 mode ((value?_model_unpack64 x).trans hx),
    deliver_of_representable _ _ hrep]

/-- The inexact flag of `roundToIntegralExact` holds exactly when the value
returned by `roundIntegral` differs from the operand (IEEE 754-2019 §5.9). -/
theorem roundToIntegralFlags_inexact_iff (mode : RoundingMode) {x : F64} {a : ℚ}
    (hx : x.toRat? = some a) :
    (FlagSpec.roundToIntegral mode true x.datum).inexact = true ↔
      (roundIntegral mode x).toRat? ≠ some a := by
  obtain ⟨n, hd⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  rw [hd, ne_eq, toRat?_eq_iff_rounded?, roundIntegral_rounded? mode hx]
  simp only [FlagSpec.roundToIntegral, Bool.true_and, ne_eq, Option.some.injEq]
  by_cases h : ((roundInt mode a : ℤ) : ℚ) = a <;> simp [h, inexactOnly, Flags.singleton, Flags.ofFunction]

end F64

theorem F64.toF32_rounded? (mode : RoundingMode) {x : F64} {a : ℚ} (hx : x.toRat? = some a) :
    (x.toF32 mode).rounded? = some (deliver .binary32 mode a) :=
  roundedOf?_unpack_packRounded .binary32 mode ((value?_model_unpack64 x).trans hx)

/-- Narrowing is inexact exactly when the binary32 value differs from the
binary64 operand. -/
theorem F64.toF32Flags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x : F64} {a : ℚ}
    (hx : x.toRat? = some a) :
    (x.toF32Flags mode tininess).inexact = true ↔ (x.toF32 mode).toRat? ≠ some a := by
  obtain ⟨nx, hdx⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  rw [toF32Flags, hdx, convert_finite, roundingFlags_inexact, ne_eq, ne_eq,
    F32.toRat?_eq_iff_rounded?, F64.toF32_rounded? mode hx, Option.some.injEq]

end Silmaril.Numeric.Ieee754
