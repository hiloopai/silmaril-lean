module

public import Silmaril.Numeric.Float.Lowering.Rounding
public import Silmaril.Numeric.Float.Lowering.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Exact results of profile operations (architecture-independent)

When the exact result of an operation is representable, every rounding
direction returns it. This file states that for the profile operations used by
multi-instruction integer conversions, on any `Profile` without input or result
flushing:

* `packRounded_isNaN`: rounding and packing a non-NaN value never produces a
  NaN encoding (the result may be infinite on overflow).
* `value?_packRounded_exact`: a representable value is packed and decoded
  unchanged (`Representable` bounds the exponent so that no overflow occurs).
* `packRounded_congr`: two unpacked values with the same nonzero rational value
  pack to the same encoding (a consequence of `roundUnpacked_congr`).
* `binary_value_core`: without flushing, `Profile.binary` on non-NaN operands
  is the core rounding whenever that rounding is not a NaN, for all four
  operations.
* `binary_value`, `convert_value`: without flushing, `Profile.binary` for
  addition or subtraction, and `Profile.convert`, on finite operands are exactly
  the core rounding of the exact result (no side condition).

Nothing here depends on an instruction set.
-/

@[expose] public section

namespace Silmaril.Numeric.Float.Lowering

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Float
open Silmaril.Numeric.Ieee754 (RoundingMode)
open Silmaril.Numeric.Ieee754.Conformance (value? dyadic ExponentNormalized)

/-- A rational exactly representable in `fmt`, given by a witness `m0 * 2^e0`
whose exponent is far enough from the top of the range that packing cannot
overflow. This is the witness form the packing lemmas below consume; it is
equivalent to the exception specification's `FlagSpec.Representable`
(`representable_iff`). -/
def Representable (fmt : Format) (q : ℚ) : Prop :=
  q = 0 ∨ ∃ m0 : ℕ, ∃ e0 : ℤ, 0 < m0 ∧ m0 < 2 ^ fmt.mantissaBits ∧ fmt.minExponent ≤ e0 ∧
    e0 + fmt.exponentBias + fmt.mantissaBitsWithoutImplicit < 2 ^ fmt.exponentBits - 1 ∧
    |q| = m0 * 2 ^ e0

/-- The exponent bound of `Representable` is `e0 ≤ maxQuantum`: the witness lies on a
grid no coarser than that of the largest binade. -/
private theorem top_iff (fmt : Format) (e0 : ℤ) :
    e0 + fmt.exponentBias + fmt.mantissaBitsWithoutImplicit < 2 ^ fmt.exponentBits - 1 ↔
      e0 ≤ Silmaril.Numeric.Ieee754.FlagSpec.maxQuantum fmt := by
  open Silmaril.Numeric.Ieee754.FlagSpec in
  have hbias : (2 : ℤ) ^ fmt.exponentBits - 1 = 2 * (fmt.exponentBias : ℤ) + 1 := by
    have he := fmt.he
    have hpos : 1 ≤ 2 ^ (fmt.exponentBits - 1) := Nat.one_le_two_pow
    have h2 : 2 ^ fmt.exponentBits = 2 * 2 ^ (fmt.exponentBits - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    unfold Format.exponentBias
    push_cast [Nat.cast_sub hpos]
    rw [show (2 : ℤ) ^ fmt.exponentBits = ((2 ^ fmt.exponentBits : ℕ) : ℤ) by push_cast; rfl, h2]
    push_cast
    ring
  have hp : (fmt.mantissaBits : ℤ) = fmt.mantissaBitsWithoutImplicit + 1 := by
    unfold Format.mantissaBits; push_cast; ring
  unfold maxQuantum emax precision
  rw [hbias, hp]
  omega

/-- The witness form is a finite value of the format in the sense of the
exception specification. -/
theorem Representable.flagSpec {fmt : Format} {q : ℚ} (h : Representable fmt q) :
    Silmaril.Numeric.Ieee754.FlagSpec.Representable fmt q := by
  open Silmaril.Numeric.Ieee754.FlagSpec in
  rcases h with rfl | ⟨m0, e0, _, hmlt, hmin, htop, habs⟩
  · exact representable_zero fmt
  have he0 : e0 ≤ maxQuantum fmt := (top_iff fmt e0).mp htop
  have hm : ((m0 : ℤ) : ℚ) ≤ ((maxSignificand fmt : ℤ) : ℚ) := by
    unfold maxSignificand
    have : (m0 : ℤ) < 2 ^ fmt.mantissaBits := by exact_mod_cast hmlt
    exact_mod_cast (by omega : (m0 : ℤ) ≤ 2 ^ fmt.mantissaBits - 1)
  refine ⟨if 0 ≤ q then (m0 : ℤ) else -(m0 : ℤ), e0, ?_, ?_, ?_, ?_⟩
  · split
    · rename_i hq
      have h' := habs
      rw [abs_of_nonneg hq] at h'
      rw [h']; push_cast; ring
    · rename_i hq
      have h' := habs
      rw [abs_of_neg (lt_of_not_ge hq)] at h'
      push_cast; linarith
  · split <;> simp only [abs_neg, Nat.abs_cast] <;> exact_mod_cast hmlt
  · rw [minQuantum_eq_minExponent]; exact hmin
  · rw [habs]
    unfold maxFinite
    have h2 : (2 : ℚ) ^ e0 ≤ 2 ^ maxQuantum fmt := zpow_le_zpow_right₀ (by norm_num) he0
    have hm' : ((m0 : ℕ) : ℚ) ≤ ((maxSignificand fmt : ℤ) : ℚ) := by exact_mod_cast hm
    exact mul_le_mul hm' h2 (by positivity) (by exact_mod_cast (maxSignificand_pos fmt).le)

/-- Every finite value of the format has a witness: shift the significand up
until it has `p` bits or the exponent reaches the subnormal exponent. -/
theorem Representable.of_flagSpec {fmt : Format} {q : ℚ}
    (h : Silmaril.Numeric.Ieee754.FlagSpec.Representable fmt q) : Representable fmt q := by
  open Silmaril.Numeric.Ieee754.FlagSpec in
  obtain ⟨n, e, hq, hn, he, hmax⟩ := h
  by_cases hn0 : n = 0
  · left; simp [hq, hn0]
  right
  set P := fmt.mantissaBits with hPdef
  set a := n.natAbs with ha_def
  have ha : 0 < a := Int.natAbs_pos.mpr hn0
  set L := Nat.log2 a with hLdef
  have haL : 2 ^ L ≤ a := Nat.log2_self_le (by omega)
  have haL' : a < 2 ^ (L + 1) := Nat.lt_log2_self
  have haP : a < 2 ^ P := by
    have : ((a : ℕ) : ℤ) < 2 ^ P := by rw [ha_def, Int.natCast_natAbs]; exact hn
    exact_mod_cast this
  have hLP : L + 1 ≤ P := by
    by_contra hc
    have : 2 ^ P ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set k : ℕ := min (P - 1 - L) (e - minQuantum fmt).toNat with hk
  have hkL : k ≤ P - 1 - L := min_le_left _ _
  have hke : (k : ℤ) ≤ e - minQuantum fmt := by
    have := min_le_right (P - 1 - L) (e - minQuantum fmt).toNat
    omega
  have habs : |q| = ((a * 2 ^ k : ℕ) : ℚ) * 2 ^ (e - k) := by
    rw [hq, abs_mul, abs_of_pos (two_zpow_pos (K := ℚ) e), ← Int.cast_abs, Int.abs_eq_natAbs]
    push_cast
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, ha_def, Nat.cast_natAbs]
    field_simp
    exact Int.cast_abs.symm
  have hmin' : minQuantum fmt ≤ maxQuantum fmt := by
    unfold minQuantum maxQuantum
    have := emin_le_emax fmt
    omega
  refine ⟨a * 2 ^ k, e - k, by positivity, ?_, ?_, ?_, habs⟩
  · calc a * 2 ^ k < 2 ^ (L + 1) * 2 ^ k := Nat.mul_lt_mul_of_pos_right haL' (by positivity)
      _ = 2 ^ (L + 1 + k) := by rw [Nat.pow_add 2 (L + 1) k]
      _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [← minQuantum_eq_minExponent]; omega
  · rw [top_iff]
    by_cases hkc : k = P - 1 - L
    · -- the significand has `p` bits, so the value bound forces the exponent bound
      by_contra hc
      have hc' : maxQuantum fmt + 1 ≤ e - k := by omega
      have hbig : (2 : ℚ) ^ (P - 1) ≤ ((a * 2 ^ k : ℕ) : ℚ) := by
        have : 2 ^ (P - 1) ≤ a * 2 ^ k := by
          calc 2 ^ (P - 1) = 2 ^ L * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
            _ ≤ a * 2 ^ k := Nat.mul_le_mul_right _ haL
        exact_mod_cast this
      have hsig : ((maxSignificand fmt : ℤ) : ℚ) < 2 ^ P := by
        unfold maxSignificand; push_cast; linarith
      have h1 : (2 : ℚ) ^ (P - 1) * 2 ^ (maxQuantum fmt + 1) ≤ |q| := by
        rw [habs]
        exact mul_le_mul hbig (zpow_le_zpow_right₀ (by norm_num) hc') (by positivity)
          (by positivity)
      have h2 : |q| < (2 : ℚ) ^ P * 2 ^ maxQuantum fmt := by
        refine lt_of_le_of_lt hmax ?_
        unfold maxFinite
        exact mul_lt_mul_of_pos_right hsig (two_zpow_pos _)
      have h3 : (2 : ℚ) ^ (P - 1) * 2 ^ (maxQuantum fmt + 1) = 2 ^ P * 2 ^ maxQuantum fmt := by
        rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
        have hP1 : P = (P - 1) + 1 := by
          have := two_le_precision fmt
          unfold precision at this
          omega
        conv_rhs => rw [hP1, pow_succ]
        ring
      linarith
    · have hk' : k = (e - minQuantum fmt).toNat := by
        rcases min_choice (P - 1 - L) (e - minQuantum fmt).toNat with h' | h'
        · exact absurd (hk.trans h') hkc
        · exact hk.trans h'
      omega

/-- The witness form and the exception specification's `Representable` agree. -/
theorem representable_iff (fmt : Format) (q : ℚ) :
    Representable fmt q ↔ Silmaril.Numeric.Ieee754.FlagSpec.Representable fmt q :=
  ⟨Representable.flagSpec, Representable.of_flagSpec⟩

private theorem roundUnpacked_ne_nan (fmt : Format) (mode : RoundingMode) {u : UnpackedFloat}
    (hu : u ≠ .notANumber) : Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode u ≠ .notANumber := by
  cases u with
  | notANumber => exact absurd rfl hu
  | infinity s => simp [Silmaril.Numeric.Ieee754.Rounding.roundUnpacked]
  | zero s => simp [Silmaril.Numeric.Ieee754.Rounding.roundUnpacked]
  | finite s m e h =>
    simp only [Silmaril.Numeric.Ieee754.Rounding.roundUnpacked,
      Silmaril.Numeric.Ieee754.Rounding.roundWithAccuracy]
    split <;> simp

/-- Rounding and packing a non-NaN value never yields a NaN encoding. -/
theorem packRounded_isNaN (fmt : Format) (mode : RoundingMode) {u : UnpackedFloat}
    (hu : u ≠ .notANumber) :
    Bits.isNaN (fmt := fmt) (Silmaril.Numeric.Ieee754.Rounding.packRounded fmt mode u) = false := by
  cases h : Bits.isNaN (fmt := fmt) (Silmaril.Numeric.Ieee754.Rounding.packRounded fmt mode u)
  · rfl
  · exfalso
    have hv := (Bits.value_eq_notANumber_iff _).mpr h
    unfold Bits.value Silmaril.Numeric.Ieee754.Rounding.packRounded at hv
    have hn := Silmaril.Numeric.Ieee754.Conformance.roundUnpacked_normalized fmt mode u
    have hne := roundUnpacked_ne_nan fmt mode (u := u) hu
    generalize Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode u = U at hv hn hne
    cases U with
    | notANumber => exact hne rfl
    | infinity s =>
      rw [Silmaril.Numeric.Ieee754.Conformance.unpack_packNormalized fmt mode _ hn trivial] at hv
      cases hv
    | zero s =>
      rw [Silmaril.Numeric.Ieee754.Conformance.unpack_packNormalized fmt mode _ hn trivial] at hv
      cases hv
    | finite s m e hm =>
      by_cases hr : (e + fmt.exponentBias + fmt.mantissaBitsWithoutImplicit).toNat <
          2 ^ fmt.exponentBits - 1
      · rw [Silmaril.Numeric.Ieee754.Conformance.unpack_packNormalized fmt mode _ hn hr] at hv
        cases hv
      · rw [Silmaril.Numeric.Ieee754.Conformance.unpack_packNormalized_overflow fmt mode s m e hm
          (by omega)] at hv
        split at hv
        · cases hv
        · simp [Silmaril.Numeric.Ieee754.Conformance.largestFinite] at hv

/-- A representable value is packed and decoded unchanged. -/
theorem value?_packRounded_exact (fmt : Format) (mode : RoundingMode) {u : UnpackedFloat} {q : ℚ}
    (hu : value? u = some q) (hq : Representable fmt q) :
    value? (unpack fmt (Silmaril.Numeric.Ieee754.Rounding.packRounded fmt mode u)) = some q := by
  cases u with
  | notANumber => simp [value?] at hu
  | infinity s => simp [value?] at hu
  | zero s =>
    simp only [value?, Option.some.injEq] at hu
    subst hu
    rw [Silmaril.Numeric.Ieee754.Rounding.packRounded_zero]
    show value? (Bits.value (fmt := fmt) (packedZero fmt s)) = _
    rw [Bits.value_packedZero]
    rfl
  | finite s M E hM =>
    simp only [value?, Option.some.injEq] at hu
    rcases hq with hq | ⟨m0, e0, h0, hm0, he0, hbig, habs⟩
    · exfalso
      rw [← hu] at hq
      simp only [Silmaril.Numeric.Ieee754.Conformance.dyadic_eq_zero_iff] at hq
      cases s <;> simp [Sign.apply] at hq <;> omega
    · have hv : (M : ℚ) * 2 ^ E = m0 * 2 ^ e0 := by
        rw [← habs, ← hu, Silmaril.Numeric.Ieee754.Conformance.abs_dyadic_sign]
      obtain ⟨m', e', h', hr, hv', hle⟩ := roundUnpacked_exact fmt mode s hM h0 hm0 he0 hv
      have inRange : Silmaril.Numeric.Ieee754.Conformance.NoExponentOverflow fmt
          (Silmaril.Numeric.Ieee754.Rounding.roundUnpacked fmt mode (.finite s M E hM)) := by
        rw [hr]
        show (e' + fmt.exponentBias + fmt.mantissaBitsWithoutImplicit).toNat < 2 ^ fmt.exponentBits - 1
        have h1 : 2 ^ 2 ≤ 2 ^ fmt.exponentBits := Nat.pow_le_pow_right (by decide) fmt.he
        generalize hN : 2 ^ fmt.exponentBits = N at h1 ⊢
        have hbig' : e0 + fmt.exponentBias + fmt.mantissaBitsWithoutImplicit < (N : ℤ) - 1 := by
          rw [← hN]; push_cast; exact hbig
        omega
      rw [Silmaril.Numeric.Ieee754.Conformance.unpack_packRounded fmt mode _ inRange, hr]
      simp only [value?, Option.some.injEq]
      rw [← hu]
      cases s <;> simp only [dyadic, Sign.apply] <;> push_cast <;> linarith [hv', hv]

/-- Two values with the same nonzero rational value round and pack alike. -/
theorem packRounded_congr (fmt : Format) (mode : RoundingMode) {u1 u2 : UnpackedFloat} {q : ℚ}
    (h1 : value? u1 = some q) (h2 : value? u2 = some q) (hq : q ≠ 0) :
    Silmaril.Numeric.Ieee754.Rounding.packRounded fmt mode u1 =
      Silmaril.Numeric.Ieee754.Rounding.packRounded fmt mode u2 := by
  unfold Silmaril.Numeric.Ieee754.Rounding.packRounded
  congr 1
  cases u1 with
  | notANumber => simp [value?] at h1
  | infinity s => simp [value?] at h1
  | zero s => simp [value?] at h1; exact absurd h1.symm hq
  | finite s1 M1 E1 hM1 =>
    cases u2 with
    | notANumber => simp [value?] at h2
    | infinity s => simp [value?] at h2
    | zero s => simp [value?] at h2; exact absurd h2.symm hq
    | finite s2 M2 E2 hM2 =>
      simp only [value?, Option.some.injEq] at h1 h2
      have hpos1 : (0 : ℚ) < M1 * 2 ^ E1 := mul_pos (by exact_mod_cast hM1) (zpow_pos (by norm_num) _)
      have hpos2 : (0 : ℚ) < M2 * 2 ^ E2 := mul_pos (by exact_mod_cast hM2) (zpow_pos (by norm_num) _)
      have hs : s1 = s2 := by
        cases s1 <;> cases s2 <;> simp only [dyadic, Sign.apply] at h1 h2 <;> push_cast at h1 h2 <;>
          first | rfl | (exfalso; linarith)
      subst hs
      apply roundUnpacked_congr
      cases s1 <;> simp only [dyadic, Sign.apply] at h1 h2 <;> push_cast at h1 h2 <;> linarith

/-! ## Profile operations without flushing -/

section Profile

variable (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false)
include hin hout

/-- Without flushing, any of the four binary operations on non-NaN operands
returns the core rounding whenever that rounding is not a NaN (it is a NaN
exactly for the invalid cases, such as `∞ - ∞` or `0 / 0`). -/
theorem binary_value_core (fmt : Format) (op : ArithOp) (mode : RoundingMode) (a b : Bits fmt)
    (hna : a.isNaN = false) (hnb : b.isNaN = false)
    (hr : Bits.isNaN (fmt := fmt) (CoreOp.round fmt mode (op.core a.value b.value)) = false) :
    (p.binary fmt op mode a b).value = CoreOp.round fmt mode (op.core a.value b.value) := by
  simp only [Profile.binary, Profile.flushInput_of_false p _ hin, Profile.nanOrElse,
    List.any_cons, List.any_nil, hna, hnb, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Profile.finish, Profile.flushSign?, hout, hr]

/-- Without flushing, addition or subtraction of finite operands is the core
rounding of the exact sum or difference. -/
theorem binary_value (fmt : Format) (op : ArithOp) (mode : RoundingMode) (a b : Bits fmt)
    {qa qb : ℚ} (ha : value? a.value = some qa) (hb : value? b.value = some qb)
    (hop : op = .add ∨ op = .sub) :
    (p.binary fmt op mode a b).value =
      Silmaril.Numeric.Ieee754.Rounding.packRounded fmt mode
        (Silmaril.Numeric.Ieee754.Rounding.addExact mode a.value
          (if op = .add then b.value else b.value.neg)) := by
  have hna : a.isNaN = false := by
    cases h : a.isNaN
    · rfl
    · rw [(Bits.value_eq_notANumber_iff a).mpr h] at ha; simp [value?] at ha
  have hnb : b.isNaN = false := by
    cases h : b.isNaN
    · rfl
    · rw [(Bits.value_eq_notANumber_iff b).mpr h] at hb; simp [value?] at hb
  have hne : Silmaril.Numeric.Ieee754.Rounding.addExact mode a.value
      (if op = .add then b.value else b.value.neg) ≠ .notANumber := by
    intro h
    have hv : value? (Silmaril.Numeric.Ieee754.Rounding.addExact mode a.value
        (if op = .add then b.value else b.value.neg)) = none := by rw [h]; rfl
    rcases hop with rfl | rfl
    · simp only [↓reduceIte] at hv
      rw [Silmaril.Numeric.Ieee754.Conformance.value?_addExact mode ha hb] at hv
      cases hv
    · simp only [reduceCtorEq, ↓reduceIte] at hv
      rw [Silmaril.Numeric.Ieee754.Conformance.value?_subExact mode ha hb] at hv
      cases hv
  simp only [Profile.binary, Profile.flushInput_of_false p _ hin, Profile.nanOrElse,
    List.any_cons, List.any_nil, hna, hnb, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Profile.finish, Profile.flushSign?, hout]
  rcases hop with rfl | rfl
  · simp only [ArithOp.core, CoreOp.round, Silmaril.Numeric.Ieee754.Rounding.addRounded,
      ↓reduceIte] at hne ⊢
    simp [packRounded_isNaN fmt mode hne]
  · simp only [ArithOp.core, CoreOp.round, Silmaril.Numeric.Ieee754.Rounding.subRounded,
      Silmaril.Numeric.Ieee754.Rounding.addRounded, reduceCtorEq, ↓reduceIte] at hne ⊢
    simp [packRounded_isNaN fmt mode hne]

/-- Without flushing, format conversion of a finite operand is the core
rounding of its value. -/
theorem convert_value (src dst : Format) (mode : RoundingMode) (x : Bits src) {q : ℚ}
    (hx : value? x.value = some q) :
    (p.convert src dst mode x).value = Silmaril.Numeric.Ieee754.Rounding.packRounded dst mode x.value := by
  have hnx : x.isNaN = false := by
    cases h : x.isNaN
    · rfl
    · rw [(Bits.value_eq_notANumber_iff x).mpr h] at hx; simp [value?] at hx
  have hne : x.value ≠ .notANumber := Bits.value_ne_notANumber hnx
  simp only [Profile.convert, Profile.flushInput_of_false p _ hin, hnx, Bool.false_eq_true,
    ↓reduceIte, Profile.finish, Profile.flushSign?, hout, CoreOp.round]
  simp [packRounded_isNaN dst mode hne]

end Profile

end Silmaril.Numeric.Float.Lowering
