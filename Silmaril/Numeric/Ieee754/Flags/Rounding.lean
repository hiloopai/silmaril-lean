module

public import Silmaril.Numeric.Ieee754.Flags.Grid
public import Silmaril.Numeric.Ieee754.Environment
public import Mathlib.Data.Int.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exceptions raised by rounding an exact result

For an operation whose exact mathematical result `x` is finite, the overflow,
underflow and inexact flags depend only on `x`, the destination format and the
rounding direction. This module defines them from `x` and IEEE 754-2019 §§4.3
and 7.4–7.6, independently of the executable rounding in
`Numeric.Ieee754.Rounding`:

* A format with `p` significand bits (including the implicit bit) and maximum
  exponent `emax` has minimum normal exponent `emin = 1 - emax` (§3.3), and
  largest finite magnitude `(2 ^ p - 1) · 2 ^ (emax - p + 1)`.
* `roundUnbounded` rounds to `p` significant bits with an unbounded exponent
  range; `roundGradual` additionally stops at the subnormal spacing
  `2 ^ (emin - p + 1)`, which is the finite result of §4.3 with gradual underflow.
* Overflow (§7.4): the magnitude of `roundUnbounded x` exceeds the largest finite
  number. The delivered result is then an infinity or the largest finite number
  of the same sign, according to the direction.
* Inexact (§7.6): the delivered result differs from `x`.
* Tininess (§7.5), under `TininessDetection`: before rounding, `0 < |x| < 2 ^ emin`;
  after rounding, `x ≠ 0` and `|roundUnbounded x| < 2 ^ emin`.
* Underflow under default handling (§7.5): the result is tiny and inexact. An
  exact tiny result raises no flag.

The main theorem, `inexact_iff_not_representable`, states that an operation is
inexact exactly when its exact result is not a finite value of the format.
Overflow implies inexactness, and underflow detected after rounding implies
underflow detected before rounding.

These definitions are generic over an ordered field with a floor function. Over
`ℚ` they are computable; over `ℝ` they also classify irrational results such as
square roots, and `roundingFlags_ratCast` shows that both agree on rationals.

Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model

universe u

/-- The two IEEE tininess-detection conventions (§7.5), the setting already
carried by `Environment`. IEEE 754-2019 lets an implementation choose either,
consistently. For later architecture profiles, the manuals state:

* x86-64: tininess after rounding. The Intel 64 and IA-32 Architectures Software
  Developer's Manual, Vol. 1, §4.9.1.5 ("Numeric Underflow Exception (#U)"),
  describes the underflow condition as a nonzero tiny result of rounding with
  unbounded exponent; the SSE exception conditions of Chapter 11 refer to it.
* RISC-V: tininess after rounding, as stated in The RISC-V Instruction Set
  Manual, Volume I: Unprivileged ISA (version 20191213), §11.4 ("Subnormal
  Arithmetic") of the F extension.
* AArch64: tininess before rounding. The `FPRoundBase` pseudocode of the Arm
  Architecture Reference Manual (DDI 0487) compares the unrounded exponent with
  the minimum normal exponent when `FPCR.AH` is 0.

These are readings of the documents, not claims about hardware behaviour. -/
abbrev Tininess := TininessDetection

/-! ## Format parameters -/

/-- Precision `p`, counting the implicit leading bit (§3.3). -/
def precision (f : Format) : ℤ := f.mantissaBits

/-- Maximum exponent `emax`, equal to the interchange bias (§3.3, §3.4). -/
def emax (f : Format) : ℤ := f.exponentBias

/-- Minimum normal exponent `emin = 1 - emax` (§3.3). -/
def emin (f : Format) : ℤ := 1 - emax f

/-- Exponent of the smallest subnormal spacing. -/
def minQuantum (f : Format) : ℤ := emin f - (precision f - 1)

/-- Exponent of the spacing of the largest binade. -/
def maxQuantum (f : Format) : ℤ := emax f - (precision f - 1)

/-- The largest integral significand, `2 ^ p - 1`. -/
def maxSignificand (f : Format) : ℤ := 2 ^ f.mantissaBits - 1

section Parameters

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The largest finite magnitude `(2 ^ p - 1) · 2 ^ (emax - p + 1)` (§3.3). -/
def maxFinite (f : Format) : K := (maxSignificand f : K) * 2 ^ maxQuantum f

theorem two_le_precision (f : Format) : 2 ≤ precision f := by
  have := f.hm
  unfold precision Format.mantissaBits
  omega

/-- The interchange bias as an integer, `2 ^ (w - 1) - 1`. -/
theorem emax_eq (f : Format) : emax f = (2 : ℤ) ^ (f.exponentBits - 1) - 1 := by
  unfold emax Format.exponentBias
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring

theorem one_le_emax (f : Format) : 1 ≤ emax f := by
  have he := f.he
  have hpow : (2 : ℤ) ≤ 2 ^ (f.exponentBits - 1) := by
    calc (2 : ℤ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ (f.exponentBits - 1) := pow_le_pow_right₀ (by decide) (by omega)
  rw [emax_eq]
  omega

theorem emin_le_emax (f : Format) : emin f ≤ emax f := by
  have := one_le_emax f
  unfold emin
  omega

theorem minQuantum_eq_minExponent (f : Format) : minQuantum f = f.minExponent := by
  unfold minQuantum emin
  rw [emax_eq]
  unfold precision Format.minExponent Format.mantissaBits
  push_cast
  ring

theorem maxSignificand_pos (f : Format) : 0 < maxSignificand f := by
  unfold maxSignificand
  have : (1 : ℤ) < 2 ^ f.mantissaBits :=
    one_lt_pow₀ (by norm_num) (by unfold Format.mantissaBits; omega)
  omega

theorem maxFinite_pos (f : Format) : (0 : K) < maxFinite f :=
  mul_pos (by exact_mod_cast maxSignificand_pos f) (two_zpow_pos _)

theorem maxFinite_lt (f : Format) : maxFinite f < (2 : K) ^ (emax f + 1) := by
  unfold maxFinite maxSignificand maxQuantum
  have hsplit : (2 : K) ^ (emax f + 1) = 2 ^ precision f * 2 ^ (emax f - (precision f - 1)) := by
    rw [← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
    congr 1
    ring
  have hp : (2 : K) ^ precision f = ((2 ^ f.mantissaBits : ℤ) : K) := by
    unfold precision
    push_cast
    exact zpow_natCast 2 _
  rw [hsplit, hp]
  exact mul_lt_mul_of_pos_right (by push_cast; linarith) (two_zpow_pos _)

/-- The smallest positive normal number `2 ^ emin` is finite. -/
theorem two_zpow_emin_le_maxFinite (f : Format) : (2 : K) ^ emin f ≤ maxFinite f := by
  unfold maxFinite maxSignificand maxQuantum
  have hp := two_le_precision f
  have hsplit : (2 : K) ^ emax f = 2 ^ (precision f - 1) * 2 ^ (emax f - (precision f - 1)) := by
    rw [← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
    congr 1
    ring
  have hlow : (2 : K) ^ emin f ≤ 2 ^ emax f :=
    zpow_le_zpow_right₀ (by norm_num) (emin_le_emax f)
  have hsig : (2 : K) ^ (precision f - 1) ≤ ((2 ^ f.mantissaBits - 1 : ℤ) : K) := by
    have hn : (f.mantissaBits : ℤ) - 1 = ((f.mantissaBits - 1 : ℕ) : ℤ) := by
      unfold precision at hp
      omega
    unfold precision
    rw [hn, zpow_natCast]
    have hk : f.mantissaBits = (f.mantissaBits - 1) + 1 := by
      unfold precision at hp
      omega
    have h1 : (1 : K) ≤ 2 ^ (f.mantissaBits - 1) := one_le_pow₀ (by norm_num)
    push_cast
    rw [hk, pow_succ]
    simp only [Nat.add_sub_cancel]
    linarith
  rw [hsplit] at hlow
  exact le_trans hlow (mul_le_mul_of_nonneg_right hsig (two_zpow_pos _).le)

/-- A finite value of the format, with its sign: an integral significand below
`2 ^ p`, a spacing no finer than the subnormal spacing, and magnitude at most
the largest finite number. Both zeros have value `0`. -/
def Representable (f : Format) (x : K) : Prop :=
  ∃ n q : ℤ, x = n * 2 ^ q ∧ |n| < 2 ^ f.mantissaBits ∧ minQuantum f ≤ q ∧ |x| ≤ maxFinite f

theorem representable_zero (f : Format) : Representable f (0 : K) :=
  ⟨0, minQuantum f, by simp, by simp, le_rfl, by simp [(maxFinite_pos f).le]⟩

theorem two_zpow_ratCast {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (e : ℤ) : (((2 : ℚ) ^ e : ℚ) : L) = (2 : L) ^ e := by
  rw [Rat.cast_zpow]
  norm_num

theorem maxFinite_ratCast {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (f : Format) : ((maxFinite f : ℚ) : L) = maxFinite f := by
  unfold maxFinite
  push_cast
  rfl

end Parameters

/-! ## Rounding to the format -/

section Rounding

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- The exponent `e` of the leading binary digit: `2 ^ e ≤ |x| < 2 ^ (e + 1)`
for nonzero `x`. -/
def leadingExponent (x : K) : ℤ := Int.log 2 |x|

theorem two_zpow_leadingExponent_le {x : K} (hx : x ≠ 0) : (2 : K) ^ leadingExponent x ≤ |x| := by
  have := Int.zpow_log_le_self (b := 2) (by norm_num) (abs_pos.mpr hx)
  simpa [leadingExponent] using this

theorem abs_lt_two_zpow_leadingExponent (x : K) : |x| < (2 : K) ^ (leadingExponent x + 1) := by
  have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) |x|
  simpa [leadingExponent] using this

theorem le_leadingExponent {x : K} {e : ℤ} (h : (2 : K) ^ e ≤ |x|) : e ≤ leadingExponent x := by
  have hx : 0 < |x| := lt_of_lt_of_le (two_zpow_pos e) h
  have := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (x := e) hx).mp (by simpa using h)
  simpa [leadingExponent] using this

theorem leadingExponent_lt {x : K} {e : ℤ} (hx : x ≠ 0) (h : |x| < (2 : K) ^ e) :
    leadingExponent x < e := by
  have := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (x := e) (abs_pos.mpr hx)).mp
    (by simpa using h)
  simpa [leadingExponent] using this

/-- The leading exponent is determined by a binade containing `|x|`. -/
theorem leadingExponent_eq {x : K} {e : ℤ} (hlo : (2 : K) ^ e ≤ |x|)
    (hhi : |x| < (2 : K) ^ (e + 1)) : leadingExponent x = e := by
  have hx : x ≠ 0 := abs_pos.mp (lt_of_lt_of_le (two_zpow_pos e) hlo)
  have h1 := le_leadingExponent hlo
  have h2 := leadingExponent_lt hx hhi
  omega

theorem leadingExponent_ratCast {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    [FloorRing L] (x : ℚ) : leadingExponent (x : L) = leadingExponent x := by
  by_cases hx : x = 0
  · subst hx
    simp [leadingExponent]
  · apply leadingExponent_eq
    · have := two_zpow_leadingExponent_le hx
      rw [← Rat.cast_abs, ← two_zpow_ratCast]
      exact Rat.cast_le.mpr this
    · have := abs_lt_two_zpow_leadingExponent x
      rw [← Rat.cast_abs, ← two_zpow_ratCast]
      exact Rat.cast_lt.mpr this

/-- Spacing exponent for rounding to `p` bits with unbounded exponent range. -/
def unboundedQuantum (f : Format) (x : K) : ℤ := leadingExponent x - (precision f - 1)

/-- Spacing exponent for rounding to the format with gradual underflow: the
spacing never falls below the subnormal spacing `2 ^ (emin - p + 1)`. -/
def quantum (f : Format) (x : K) : ℤ := max (leadingExponent x) (emin f) - (precision f - 1)

/-- Round to `p` significant bits with unbounded exponent range. This is the
reference value for overflow (§7.4) and for tininess after rounding (§7.5). -/
def roundUnbounded (f : Format) (mode : RoundingMode) (x : K) : K :=
  roundAt mode (unboundedQuantum f x) x

/-- Round to the format's precision and subnormal spacing, before the
largest-finite bound is applied (§4.3). -/
def roundGradual (f : Format) (mode : RoundingMode) (x : K) : K :=
  roundAt mode (quantum f x) x

omit [IsStrictOrderedRing K] in
theorem unboundedQuantum_le_quantum (f : Format) (x : K) : unboundedQuantum f x ≤ quantum f x := by
  unfold unboundedQuantum quantum
  omega

omit [IsStrictOrderedRing K] in
theorem minQuantum_le_quantum (f : Format) (x : K) : minQuantum f ≤ quantum f x := by
  unfold minQuantum quantum
  omega

@[simp] theorem roundUnbounded_zero (f : Format) (mode : RoundingMode) :
    roundUnbounded f mode (0 : K) = 0 := roundAt_zero _ _

@[simp] theorem roundGradual_zero (f : Format) (mode : RoundingMode) :
    roundGradual f mode (0 : K) = 0 := roundAt_zero _ _

/-- A nonzero value with a `p`-bit significand on a grid no finer than the
subnormal spacing lies on the format's grid for its own binade. -/
theorem quantum_le_of_significand {f : Format} {n q : ℤ} (hn : n ≠ 0)
    (hnb : |n| < 2 ^ f.mantissaBits) (hq : minQuantum f ≤ q) :
    quantum f ((n : K) * 2 ^ q) ≤ q := by
  have hx : (n : K) * 2 ^ q ≠ 0 := mul_ne_zero (by exact_mod_cast hn) (two_zpow_ne_zero q)
  have habs : |(n : K) * 2 ^ q| < (2 : K) ^ (q + precision f) := by
    rw [abs_mul, abs_of_pos (two_zpow_pos (K := K) q), zpow_add₀ (by norm_num : (2 : K) ≠ 0), mul_comm]
    apply mul_lt_mul_of_pos_left _ (two_zpow_pos q)
    unfold precision
    rw [zpow_natCast]
    exact_mod_cast hnb
  have hlead := leadingExponent_lt hx habs
  unfold quantum
  unfold minQuantum at hq
  omega

theorem roundGradual_of_representable (f : Format) (mode : RoundingMode) {x : K}
    (h : Representable f x) : roundGradual f mode x = x := by
  obtain ⟨n, q, rfl, hnb, hq, -⟩ := h
  by_cases hn : n = 0
  · subst hn
    simp
  · obtain ⟨m, hm⟩ := intMul_of_le (K := K) (quantum_le_of_significand (K := K) hn hnb hq) n
    unfold roundGradual
    rw [congrArg (roundAt mode (quantum f ((n : K) * 2 ^ q))) hm, roundAt_intMul, ← hm]

theorem roundUnbounded_of_representable (f : Format) (mode : RoundingMode) {x : K}
    (h : Representable f x) : roundUnbounded f mode x = x := by
  obtain ⟨n, q, rfl, hnb, hq, -⟩ := h
  by_cases hn : n = 0
  · subst hn
    simp
  · have hle := le_trans (unboundedQuantum_le_quantum f ((n : K) * 2 ^ q))
      (quantum_le_of_significand (K := K) hn hnb hq)
    obtain ⟨m, hm⟩ := intMul_of_le (K := K) hle n
    unfold roundUnbounded
    rw [congrArg (roundAt mode (unboundedQuantum f ((n : K) * 2 ^ q))) hm, roundAt_intMul, ← hm]

/-! ## Overflow, delivered results and inexactness -/

/-- Overflow (§7.4): rounding with unbounded exponent range exceeds the largest
finite magnitude. -/
def Overflows (f : Format) (mode : RoundingMode) (x : K) : Prop :=
  maxFinite f < |roundUnbounded f mode x|

instance (f : Format) (mode : RoundingMode) (x : K) : Decidable (Overflows f mode x) :=
  inferInstanceAs (Decidable (_ < _))

/-- Whether default overflow handling delivers an infinity, rather than the
largest finite number, for a result of the given sign (§7.4). -/
def overflowsToInfinity (mode : RoundingMode) (negative : Bool) : Bool :=
  match mode with
  | .nearestTiesToEven | .nearestTiesToAway => true
  | .towardZero => false
  | .towardPositive => !negative
  | .towardNegative => negative

/-- A delivered floating-point result: a finite value or a signed infinity.
The sign of a zero is not recorded; exception classification does not need it. -/
inductive Rounded (K : Type u) where
  | finite (value : K)
  | infinite (negative : Bool)
  deriving DecidableEq, Repr

/-- The result delivered under default exception handling for an exact finite
result `x` (§§4.3, 7.4). -/
def deliver (f : Format) (mode : RoundingMode) (x : K) : Rounded K :=
  if Overflows f mode x then
    if overflowsToInfinity mode (decide (x < 0)) then .infinite (decide (x < 0))
    else .finite (if x < 0 then -maxFinite f else maxFinite f)
  else .finite (roundGradual f mode x)

/-- Inexact (§7.6): the delivered result differs from the exact result. -/
def Inexact (f : Format) (mode : RoundingMode) (x : K) : Prop :=
  deliver f mode x ≠ .finite x

instance (f : Format) (mode : RoundingMode) (x : K) : Decidable (Inexact f mode x) :=
  inferInstanceAs (Decidable (¬ _ = _))

theorem not_overflows_of_abs_le (f : Format) (mode : RoundingMode) {x : K}
    (h : |x| ≤ maxFinite f) : ¬ Overflows f mode x := by
  unfold Overflows
  by_cases hx : x = 0
  · subst hx
    simp [(maxFinite_pos f).le]
  · have hlead : leadingExponent x < emax f + 1 :=
      leadingExponent_lt hx (lt_of_le_of_lt h (maxFinite_lt f))
    have hle : unboundedQuantum f x ≤ maxQuantum f := by
      unfold unboundedQuantum maxQuantum
      omega
    obtain ⟨m, hm⟩ := intMul_of_le (K := K) hle (maxSignificand f)
    have := abs_roundAt_le mode (unboundedQuantum f x) m (by rw [← hm]; exact h)
    unfold roundUnbounded
    rw [← hm] at this
    exact not_lt.mpr this

/-- An overflowing exact result exceeds the largest finite magnitude. -/
theorem maxFinite_lt_abs_of_overflows {f : Format} {mode : RoundingMode} {x : K}
    (h : Overflows f mode x) : maxFinite f < |x| :=
  lt_of_not_ge fun hle => not_overflows_of_abs_le f mode hle h

/-- Overflow always implies inexactness (§7.4). -/
theorem inexact_of_overflows {f : Format} {mode : RoundingMode} {x : K}
    (h : Overflows f mode x) : Inexact f mode x := by
  have hbig := maxFinite_lt_abs_of_overflows h
  unfold Inexact deliver
  simp only [h, ↓reduceIte]
  split
  · intro heq
    cases heq
  · intro heq
    have hv : (if x < 0 then -maxFinite f else maxFinite f) = x := Rounded.finite.inj heq
    have : |x| = maxFinite f := by
      rw [← hv]
      split <;> simp [abs_of_pos (maxFinite_pos (K := K) f)]
    linarith

omit [IsStrictOrderedRing K] in
theorem deliver_of_not_overflows {f : Format} {mode : RoundingMode} {x : K}
    (h : ¬ Overflows f mode x) : deliver f mode x = .finite (roundGradual f mode x) := by
  unfold deliver
  simp only [h, ↓reduceIte]

/-- A finite value of the format is delivered unchanged. -/
theorem deliver_of_representable (f : Format) (mode : RoundingMode) {x : K}
    (h : Representable f x) : deliver f mode x = .finite x := by
  have hmax : |x| ≤ maxFinite f := by
    obtain ⟨_, _, _, _, _, hmax⟩ := h
    exact hmax
  rw [deliver_of_not_overflows (not_overflows_of_abs_le f mode hmax),
    roundGradual_of_representable f mode h]

/-- Inexactness splits into overflow and a rounding error in the finite range. -/
theorem inexact_iff_overflows_or (f : Format) (mode : RoundingMode) (x : K) :
    Inexact f mode x ↔ Overflows f mode x ∨ roundGradual f mode x ≠ x := by
  by_cases ho : Overflows f mode x
  · exact ⟨fun _ => Or.inl ho, fun _ => inexact_of_overflows ho⟩
  · unfold Inexact
    rw [deliver_of_not_overflows ho]
    simp only [ne_eq, Rounded.finite.injEq, ho, false_or]

/-- Inexactness is exactly non-representability of the exact result. -/
theorem inexact_iff_not_representable (f : Format) (mode : RoundingMode) (x : K) :
    Inexact f mode x ↔ ¬ Representable f x := by
  constructor
  · intro hin hrep
    exact hin (deliver_of_representable f mode hrep)
  · intro hrep hexact
    apply hrep
    have hno : ¬ Overflows f mode x := fun ho => inexact_of_overflows ho hexact
    rw [deliver_of_not_overflows hno] at hexact
    have hfix : roundGradual f mode x = x := Rounded.finite.inj hexact
    by_cases hx : x = 0
    · subst hx
      exact representable_zero f
    obtain ⟨n, hn⟩ := (roundAt_eq_self_iff mode (quantum f x) x).mp hfix
    refine ⟨n, quantum f x, hn, ?_, minQuantum_le_quantum f x, ?_⟩
    · -- The significand has at most `p` bits.
      have hbound := abs_lt_two_zpow_leadingExponent x
      have hq : leadingExponent x + 1 ≤ precision f + quantum f x := by
        unfold quantum
        omega
      have hmono : (2 : K) ^ (leadingExponent x + 1) ≤ 2 ^ (precision f + quantum f x) :=
        zpow_le_zpow_right₀ (by norm_num) hq
      have habs : |x| = ((|n| : ℤ) : K) * 2 ^ quantum f x := by
        rw [congrArg (fun y : K => |y|) hn, abs_mul, abs_of_pos (two_zpow_pos (K := K) (quantum f x)),
          Int.cast_abs]
      rw [zpow_add₀ (by norm_num : (2 : K) ≠ 0) (precision f) (quantum f x)] at hmono
      have hlt : ((|n| : ℤ) : K) * 2 ^ quantum f x < 2 ^ precision f * 2 ^ quantum f x := by
        rw [← habs]
        exact lt_of_lt_of_le hbound hmono
      have := lt_of_mul_lt_mul_right hlt (two_zpow_pos (K := K) (quantum f x)).le
      unfold precision at this
      rw [zpow_natCast] at this
      exact_mod_cast this
    · -- No overflow means the unbounded rounding of `x`, which is `x`, is finite.
      have hfixU : roundUnbounded f mode x = x := by
        obtain ⟨m, hm⟩ := intMul_of_le (K := K) (unboundedQuantum_le_quantum f x) n
        have hx' : x = m * 2 ^ unboundedQuantum f x := hn.trans hm
        unfold roundUnbounded
        rw [congrArg (roundAt mode (unboundedQuantum f x)) hx', roundAt_intMul]
        exact hx'.symm
      unfold Overflows at hno
      rw [hfixU] at hno
      exact not_lt.mp hno

theorem not_inexact_iff_representable (f : Format) (mode : RoundingMode) (x : K) :
    ¬ Inexact f mode x ↔ Representable f x := by
  rw [inexact_iff_not_representable, not_not]

/-! ## Tininess and underflow -/

/-- The magnitude compared with `2 ^ emin` by each tininess convention (§7.5). -/
def tininessMagnitude (f : Format) (tininess : Tininess) (mode : RoundingMode) (x : K) : K :=
  match tininess with
  | .beforeRounding => |x|
  | .afterRounding => |roundUnbounded f mode x|

/-- A nonzero result is tiny when the selected magnitude lies strictly below the
smallest positive normal number `2 ^ emin` (§7.5). -/
def Tiny (f : Format) (tininess : Tininess) (mode : RoundingMode) (x : K) : Prop :=
  x ≠ 0 ∧ tininessMagnitude f tininess mode x < 2 ^ emin f

instance (f : Format) (tininess : Tininess) (mode : RoundingMode) (x : K) :
    Decidable (Tiny f tininess mode x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Default underflow (§7.5): the result is tiny and inexact. -/
def Underflows (f : Format) (tininess : Tininess) (mode : RoundingMode) (x : K) : Prop :=
  Tiny f tininess mode x ∧ Inexact f mode x

instance (f : Format) (tininess : Tininess) (mode : RoundingMode) (x : K) :
    Decidable (Underflows f tininess mode x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Tininess after rounding implies tininess before rounding: rounding a
magnitude of at least `2 ^ emin` to `p` bits cannot fall below `2 ^ emin`. -/
theorem tiny_before_of_after {f : Format} {mode : RoundingMode} {x : K}
    (h : Tiny f .afterRounding mode x) : Tiny f .beforeRounding mode x := by
  obtain ⟨hx, hsmall⟩ := h
  refine ⟨hx, lt_of_not_ge fun hbig => ?_⟩
  simp only [tininessMagnitude] at hsmall hbig
  apply not_le.mpr hsmall
  by_cases hq : unboundedQuantum f x ≤ emin f
  · exact le_abs_roundAt mode hq hbig
  · have hp := two_le_precision f
    have hql : unboundedQuantum f x ≤ leadingExponent x := by
      unfold unboundedQuantum
      omega
    have hle : emin f ≤ leadingExponent x := by
      unfold unboundedQuantum at hq
      omega
    exact le_trans (zpow_le_zpow_right₀ (by norm_num) hle)
      (le_abs_roundAt mode hql (two_zpow_leadingExponent_le hx))

theorem underflows_before_of_after {f : Format} {mode : RoundingMode} {x : K}
    (h : Underflows f .afterRounding mode x) : Underflows f .beforeRounding mode x :=
  ⟨tiny_before_of_after h.1, h.2⟩

/-- A tiny result never overflows. -/
theorem not_overflows_of_tiny {f : Format} {tininess : Tininess} {mode : RoundingMode} {x : K}
    (h : Tiny f tininess mode x) : ¬ Overflows f mode x := by
  have hmin := two_zpow_emin_le_maxFinite (K := K) f
  cases tininess with
  | beforeRounding =>
    exact not_overflows_of_abs_le f mode (le_trans (le_of_lt h.2) hmin)
  | afterRounding =>
    exact not_lt.mpr (le_trans (le_of_lt h.2) hmin)

omit [IsStrictOrderedRing K] in
theorem inexact_of_underflows {f : Format} {tininess : Tininess} {mode : RoundingMode} {x : K}
    (h : Underflows f tininess mode x) : Inexact f mode x := h.2

/-! ## The flags raised by the rounding stage -/

/-- Overflow, underflow and inexact for an exact finite result `x` under default
exception handling (§§7.4–7.6). The invalid and divide-by-zero exceptions are
determined by the operands and never arise in this stage. -/
def roundingFlags (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : K) : Flags where
  overflow := decide (Overflows f mode x)
  underflow := decide (Underflows f tininess mode x)
  inexact := decide (Inexact f mode x)

omit [IsStrictOrderedRing K] in
@[simp] theorem roundingFlags_invalidOperation (f : Format) (mode : RoundingMode)
    (tininess : Tininess) (x : K) : (roundingFlags f mode tininess x).invalidOperation = false := rfl

omit [IsStrictOrderedRing K] in
@[simp] theorem roundingFlags_divisionByZero (f : Format) (mode : RoundingMode)
    (tininess : Tininess) (x : K) : (roundingFlags f mode tininess x).divisionByZero = false := rfl

omit [IsStrictOrderedRing K] in
theorem roundingFlags_overflow (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : K) :
    (roundingFlags f mode tininess x).overflow = true ↔ Overflows f mode x :=
  decide_eq_true_iff

omit [IsStrictOrderedRing K] in
theorem roundingFlags_underflow (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : K) :
    (roundingFlags f mode tininess x).underflow = true ↔ Underflows f tininess mode x :=
  decide_eq_true_iff

omit [IsStrictOrderedRing K] in
/-- The inexact flag is raised exactly when the delivered result differs from
the exact result. -/
theorem roundingFlags_inexact (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : K) :
    (roundingFlags f mode tininess x).inexact = true ↔ deliver f mode x ≠ .finite x :=
  decide_eq_true_iff

/-- The inexact flag is raised exactly when the exact result is not a finite
value of the destination format. -/
theorem roundingFlags_inexact_iff_not_representable (f : Format) (mode : RoundingMode)
    (tininess : Tininess) (x : K) :
    (roundingFlags f mode tininess x).inexact = true ↔ ¬ Representable f x :=
  decide_eq_true_iff.trans (inexact_iff_not_representable f mode x)

theorem roundingFlags_inexact_of_overflow {f : Format} {mode : RoundingMode}
    {tininess : Tininess} {x : K} (h : (roundingFlags f mode tininess x).overflow = true) :
    (roundingFlags f mode tininess x).inexact = true := by
  rw [roundingFlags_overflow] at h
  exact decide_eq_true_iff.mpr (inexact_of_overflows h)

omit [IsStrictOrderedRing K] in
theorem roundingFlags_inexact_of_underflow {f : Format} {mode : RoundingMode}
    {tininess : Tininess} {x : K} (h : (roundingFlags f mode tininess x).underflow = true) :
    (roundingFlags f mode tininess x).inexact = true := by
  rw [roundingFlags_underflow] at h
  exact decide_eq_true_iff.mpr h.2

/-- Overflow and underflow are never raised together. -/
theorem roundingFlags_not_overflow_and_underflow (f : Format) (mode : RoundingMode)
    (tininess : Tininess) (x : K) :
    ¬ ((roundingFlags f mode tininess x).overflow = true ∧
      (roundingFlags f mode tininess x).underflow = true) := by
  rintro ⟨ho, hu⟩
  rw [roundingFlags_overflow] at ho
  rw [roundingFlags_underflow] at hu
  exact not_overflows_of_tiny hu.1 ho

/-- A representable exact result raises no flag. In particular, an exact tiny
result does not raise underflow (§7.5). -/
theorem roundingFlags_of_representable (f : Format) (mode : RoundingMode)
    (tininess : Tininess) {x : K} (h : Representable f x) :
    roundingFlags f mode tininess x = Flags.empty := by
  have hex : ¬ Inexact f mode x := (not_inexact_iff_representable f mode x).mpr h
  have hno : ¬ Overflows f mode x := fun ho => hex (inexact_of_overflows ho)
  simp [roundingFlags, Underflows, hex, hno, Flags.empty]

@[simp] theorem roundingFlags_zero (f : Format) (mode : RoundingMode) (tininess : Tininess) :
    roundingFlags f mode tininess (0 : K) = Flags.empty :=
  roundingFlags_of_representable f mode tininess (representable_zero f)

/-- Underflow detected after rounding is also detected before rounding. -/
theorem roundingFlags_underflow_before_of_after {f : Format} {mode : RoundingMode} {x : K}
    (h : (roundingFlags f mode .afterRounding x).underflow = true) :
    (roundingFlags f mode .beforeRounding x).underflow = true := by
  rw [roundingFlags_underflow] at h ⊢
  exact underflows_before_of_after h

omit [IsStrictOrderedRing K] in
/-- The tininess convention changes only the underflow flag. -/
theorem roundingFlags_tininess_eq (f : Format) (mode : RoundingMode) (t₁ t₂ : Tininess) (x : K) :
    (roundingFlags f mode t₁ x).clear (Flags.singleton .underflow) =
      (roundingFlags f mode t₂ x).clear (Flags.singleton .underflow) := by
  ext e
  rw [Flags.contains_clear, Flags.contains_clear]
  cases e <;> simp [roundingFlags, Flags.contains, Flags.singleton, Flags.ofFunction]

end Rounding

/-! ## Rationals in larger fields -/

section Cast

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FloorRing L]

theorem roundUnbounded_ratCast (f : Format) (mode : RoundingMode) (x : ℚ) :
    roundUnbounded f mode (x : L) = ((roundUnbounded f mode x : ℚ) : L) := by
  unfold roundUnbounded unboundedQuantum
  rw [leadingExponent_ratCast, roundAt_ratCast]

theorem roundGradual_ratCast (f : Format) (mode : RoundingMode) (x : ℚ) :
    roundGradual f mode (x : L) = ((roundGradual f mode x : ℚ) : L) := by
  unfold roundGradual quantum
  rw [leadingExponent_ratCast, roundAt_ratCast]

theorem overflows_ratCast (f : Format) (mode : RoundingMode) (x : ℚ) :
    Overflows f mode (x : L) ↔ Overflows f mode x := by
  unfold Overflows
  rw [roundUnbounded_ratCast, ← maxFinite_ratCast (L := L), ← Rat.cast_abs, Rat.cast_lt]

theorem inexact_ratCast (f : Format) (mode : RoundingMode) (x : ℚ) :
    Inexact f mode (x : L) ↔ Inexact f mode x := by
  by_cases ho : Overflows f mode x
  · have ho' : Overflows f mode (x : L) := (overflows_ratCast f mode x).mpr ho
    exact ⟨fun _ => inexact_of_overflows ho, fun _ => inexact_of_overflows ho'⟩
  · have ho' : ¬ Overflows f mode (x : L) := fun h => ho ((overflows_ratCast f mode x).mp h)
    unfold Inexact
    rw [deliver_of_not_overflows ho, deliver_of_not_overflows ho', roundGradual_ratCast]
    simp only [ne_eq, Rounded.finite.injEq, Rat.cast_inj]

theorem tiny_ratCast (f : Format) (tininess : Tininess) (mode : RoundingMode) (x : ℚ) :
    Tiny f tininess mode (x : L) ↔ Tiny f tininess mode x := by
  have h2 : (2 : L) ^ emin f = (((2 : ℚ) ^ emin f : ℚ) : L) := by push_cast; rfl
  unfold Tiny
  cases tininess <;>
    simp only [tininessMagnitude, roundUnbounded_ratCast, ← Rat.cast_abs, h2, Rat.cast_lt,
      ne_eq, Rat.cast_eq_zero]

/-- The flags of a rational exact result do not depend on the ordered field in
which it is classified. Hence the computable classification over `ℚ` agrees
with the classification of the same real number. -/
theorem roundingFlags_ratCast (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : ℚ) :
    roundingFlags f mode tininess (x : L) = roundingFlags f mode tininess x := by
  unfold roundingFlags Underflows
  congr 1
  · exact decide_eq_decide.mpr (overflows_ratCast f mode x)
  · exact decide_eq_decide.mpr
      (and_congr (tiny_ratCast f tininess mode x) (inexact_ratCast f mode x))
  · exact decide_eq_decide.mpr (inexact_ratCast f mode x)

end Cast

end Silmaril.Numeric.Ieee754.FlagSpec
