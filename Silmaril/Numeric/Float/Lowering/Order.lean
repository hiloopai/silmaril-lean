module

public import Silmaril.Numeric.Float.Wasm
public import Silmaril.Numeric.Float.Lowering.Compare
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Order and integer range of decoded encodings (architecture-independent)

`UnpackedFloat.compare` orders canonical values by exponent and then mantissa.
This file proves that on decoded encodings this is the numerical order of the
extended value `ext` (the rational value, `⊤` for `+∞`, `⊥` for `-∞`), and
characterizes WebAssembly's trapping truncation range in the same terms:

* `compare_value`: for non-NaN encodings, `compare` is `compare` of `ext`.
* `fromFloat_isSome_iff`: truncation toward zero into an integer format with
  bounds `lo ≤ 0 ≤ hi` succeeds exactly when `lo - 1 < ext x < hi + 1`.
* `le_iff_pred_lt`: for an integer bound `L ≤ -2^(P-1)` (with `P` the
  precision), `L ≤ ext x` iff `L - 1 < ext x`, because every value of that
  magnitude is an integer. This is what lets a range check against `-2^31`
  or `-2^63` use a non-strict comparison.

These are the facts needed to verify range guards and masks built from
floating-point comparisons (x86 `UCOMISS`/`CMPSS`, and equally RISC-V
`FLT`/`FLE` or AArch64 `FCMP`). Nothing here depends on an instruction set.
-/

@[expose] public section

namespace Silmaril.Numeric.Float.Lowering

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Float
open Silmaril.Numeric.Ieee754 (RoundingMode)
open Silmaril.Numeric.Ieee754.Conformance (value? dyadic ExponentNormalized)
open Silmaril.Numeric.Ieee754.FlagSpec (roundInt)

/-- A rational as an extended value. -/
def ofRat (q : ℚ) : WithBot (WithTop ℚ) := ((q : WithTop ℚ) : WithBot (WithTop ℚ))

/-- The extended value of an unpacked float: its rational value, `⊤` for `+∞`
and `⊥` for `-∞`. NaN is also sent to `⊥`; statements exclude it
separately. -/
def ext : UnpackedFloat → WithBot (WithTop ℚ)
  | .zero _ => ofRat 0
  | .finite s m e _ => ofRat (dyadic (s.apply m) e)
  | .infinity .positive => ((⊤ : WithTop ℚ) : WithBot (WithTop ℚ))
  | .infinity .negative => ⊥
  | .notANumber => ⊥

@[simp] theorem ofRat_lt_ofRat {a b : ℚ} : ofRat a < ofRat b ↔ a < b := by
  simp [ofRat]

@[simp] theorem ofRat_le_ofRat {a b : ℚ} : ofRat a ≤ ofRat b ↔ a ≤ b := by
  simp [ofRat]

@[simp] theorem ofRat_inj {a b : ℚ} : ofRat a = ofRat b ↔ a = b := by
  simp [ofRat]

@[simp] theorem bot_lt_ofRat (a : ℚ) : ⊥ < ofRat a := WithBot.bot_lt_coe _

@[simp] theorem ofRat_lt_top (a : ℚ) : ofRat a < ((⊤ : WithTop ℚ) : WithBot (WithTop ℚ)) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top a)

@[simp] theorem ofRat_ne_bot (a : ℚ) : ofRat a ≠ ⊥ := WithBot.coe_ne_bot

theorem compare_ofRat (a b : ℚ) : compare (ofRat a) (ofRat b) = compare a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (ofRat_lt_ofRat.mpr h)]
  · simp
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (ofRat_lt_ofRat.mpr h)]

/-! ## Canonical order -/

private theorem lt_of_exp_lt {P : ℕ} (hP : 1 ≤ P) {m1 m2 : ℕ} {e1 e2 : ℤ}
    (h1 : m1 < 2 ^ P) (h2 : 2 ^ (P - 1) ≤ m2) (he : e1 < e2) :
    (m1 : ℚ) * 2 ^ e1 < m2 * 2 ^ e2 := by
  have q1 : (m1 : ℚ) < 2 ^ P := by exact_mod_cast h1
  have q2 : (2 : ℚ) ^ (P - 1) ≤ m2 := by exact_mod_cast h2
  have hz : (2 : ℚ) ^ e1 * 2 ≤ 2 ^ e2 := by
    rw [← zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpow : (2 : ℚ) ^ P = 2 ^ (P - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ e1 := zpow_pos (by norm_num) _
  calc (m1 : ℚ) * 2 ^ e1 < 2 ^ P * 2 ^ e1 := mul_lt_mul_of_pos_right q1 hpos
    _ = 2 ^ (P - 1) * (2 ^ e1 * 2) := by rw [hpow]; ring
    _ ≤ 2 ^ (P - 1) * 2 ^ e2 := by gcongr
    _ ≤ m2 * 2 ^ e2 := by gcongr

/-- Exponent-then-mantissa comparison of canonical positive values is their
numerical comparison. -/
theorem lex_compare (fmt : Format) {m1 m2 : ℕ} {e1 e2 : ℤ} (s1 s2 : Sign) (hm1 : 0 < m1)
    (hm2 : 0 < m2) (n1 : ExponentNormalized fmt (.finite s1 m1 e1 hm1))
    (n2 : ExponentNormalized fmt (.finite s2 m2 e2 hm2)) :
    (compare e1 e2).then (compare m1 m2) = compare ((m1 : ℚ) * 2 ^ e1) ((m2 : ℚ) * 2 ^ e2) := by
  have b1 := n1.finite_bounds fmt s1 m1 e1 hm1
  have b2 := n2.finite_bounds fmt s2 m2 e2 hm2
  have hP : 1 ≤ fmt.mantissaBits := by unfold Format.mantissaBits; omega
  rcases lt_trichotomy e1 e2 with h | rfl | h
  · have key := lt_of_exp_lt hP b1.2.1 (b2.2.2.resolve_left (by omega)) h
    rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr key]
    rfl
  · rw [compare_eq_iff_eq.mpr rfl, Ordering.eq_then]
    have hpos : (0 : ℚ) < 2 ^ e1 := zpow_pos (by norm_num) _
    rcases lt_trichotomy m1 m2 with hm | rfl | hm
    · rw [compare_lt_iff_lt.mpr hm, compare_lt_iff_lt.mpr
        (mul_lt_mul_of_pos_right (by exact_mod_cast hm) hpos)]
    · simp
    · rw [compare_gt_iff_gt.mpr hm, compare_gt_iff_gt.mpr
        (mul_lt_mul_of_pos_right (by exact_mod_cast hm) hpos)]
  · have key := lt_of_exp_lt hP b2.2.1 (b1.2.2.resolve_left (by omega)) h
    rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr key]
    rfl

private theorem dyadic_pos (m : ℕ) (e : ℤ) : dyadic (Sign.positive.apply m) e = (m : ℚ) * 2 ^ e := by
  simp [dyadic, Sign.apply]

private theorem dyadic_neg (m : ℕ) (e : ℤ) :
    dyadic (Sign.negative.apply m) e = -((m : ℚ) * 2 ^ e) := by
  simp [dyadic, Sign.apply]

private theorem mul_zpow_pos {m : ℕ} (hm : 0 < m) (e : ℤ) : (0 : ℚ) < m * 2 ^ e :=
  mul_pos (by exact_mod_cast hm) (zpow_pos (by norm_num) _)

private theorem compare_neg_neg (a b : ℚ) : compare (-a) (-b) = compare b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [compare_gt_iff_gt.mpr (neg_lt_neg h), compare_gt_iff_gt.mpr h]
  · simp
  · rw [compare_lt_iff_lt.mpr (neg_lt_neg h), compare_lt_iff_lt.mpr h]

/-- On canonical non-NaN values, `UnpackedFloat.compare` is the order of `ext`. -/
theorem compare_canonical {fmt : Format} {u v : UnpackedFloat} (hu : ExponentNormalized fmt u)
    (hv : ExponentNormalized fmt v) (hun : u ≠ .notANumber) (hvn : v ≠ .notANumber) :
    u.compare v = some (compare (ext u) (ext v)) := by
  rcases u with ⟨su⟩ | _ | ⟨su⟩ | ⟨su, mu, eu, hmu⟩ <;>
  rcases v with ⟨sv⟩ | _ | ⟨sv⟩ | ⟨sv, mv, ev, hmv⟩ <;>
  (try exact absurd rfl hun) <;> (try exact absurd rfl hvn)
  -- infinity, infinity
  · cases su <;> cases sv <;> simp [UnpackedFloat.compare, ext, compare, compareOfLessAndEq]
  -- infinity, zero
  · cases su
    · simp only [UnpackedFloat.compare, ext]
      rw [compare_lt_iff_lt.mpr (bot_lt_ofRat 0)]
    · simp only [UnpackedFloat.compare, ext]
      rw [compare_gt_iff_gt.mpr (ofRat_lt_top 0)]
  -- infinity, finite
  · cases su
    · simp only [UnpackedFloat.compare, ext]
      rw [compare_lt_iff_lt.mpr (bot_lt_ofRat _)]
    · simp only [UnpackedFloat.compare, ext]
      rw [compare_gt_iff_gt.mpr (ofRat_lt_top _)]
  -- zero, infinity
  · cases sv
    · simp only [UnpackedFloat.compare, ext]
      rw [compare_gt_iff_gt.mpr (bot_lt_ofRat 0)]
    · simp only [UnpackedFloat.compare, ext]
      rw [compare_lt_iff_lt.mpr (ofRat_lt_top 0)]
  -- zero, zero
  · simp [UnpackedFloat.compare, ext]
  -- zero, finite
  · cases sv
    · simp only [UnpackedFloat.compare, ext, compare_ofRat, dyadic_neg]
      rw [compare_gt_iff_gt.mpr (by linarith [mul_zpow_pos hmv ev])]
    · simp only [UnpackedFloat.compare, ext, compare_ofRat, dyadic_pos]
      rw [compare_lt_iff_lt.mpr (mul_zpow_pos hmv ev)]
  -- finite, infinity
  · cases sv
    · cases su <;> simp only [UnpackedFloat.compare, ext] <;>
        rw [compare_gt_iff_gt.mpr (bot_lt_ofRat _)]
    · cases su <;> simp only [UnpackedFloat.compare, ext] <;>
        rw [compare_lt_iff_lt.mpr (ofRat_lt_top _)]
  -- finite, zero
  · cases su
    · simp only [UnpackedFloat.compare, ext, compare_ofRat, dyadic_neg]
      rw [compare_lt_iff_lt.mpr (by linarith [mul_zpow_pos hmu eu])]
    · simp only [UnpackedFloat.compare, ext, compare_ofRat, dyadic_pos]
      rw [compare_gt_iff_gt.mpr (mul_zpow_pos hmu eu)]
  -- finite, finite
  · have lex := lex_compare fmt su sv hmu hmv hu hv
    cases su <;> cases sv <;>
      simp only [UnpackedFloat.compare, ext, compare_ofRat, dyadic_neg, dyadic_pos, Option.some.injEq]
    · rw [compare_neg_neg, lex, ← Std.OrientedOrd.eq_swap]
    · rw [compare_lt_iff_lt.mpr (by linarith [mul_zpow_pos hmu eu, mul_zpow_pos hmv ev])]
    · rw [compare_gt_iff_gt.mpr (by linarith [mul_zpow_pos hmu eu, mul_zpow_pos hmv ev])]
    · exact lex

/-- Decoded encodings are canonical. -/
theorem value_normalized {fmt : Format} (b : Bits fmt) : ExponentNormalized fmt b.value :=
  Silmaril.Numeric.Ieee754.Conformance.unpack_exponent_normalized fmt b

/-- For non-NaN encodings, `compare` of the decoded values is the order of their
extended values. -/
theorem compare_value {fmt : Format} {a b : Bits fmt} (ha : a.isNaN = false) (hb : b.isNaN = false) :
    a.value.compare b.value = some (compare (ext a.value) (ext b.value)) :=
  compare_canonical (value_normalized a) (value_normalized b) (Bits.value_ne_notANumber ha)
    (Bits.value_ne_notANumber hb)

/-! ## Integer truncation range -/

/-- The value `value?` and the extended value agree on finite values. -/
theorem value?_eq_some_iff {u : UnpackedFloat} {q : ℚ} :
    value? u = some q ↔ (u ≠ .notANumber ∧ ext u = ofRat q) := by
  rcases u with ⟨s⟩ | _ | ⟨s⟩ | ⟨s, m, e, hm⟩
  · cases s <;> simp [value?, ext, ofRat]
  · simp [value?]
  · simp [value?, ext, eq_comm]
  · simp [value?, ext, eq_comm]

/-- Truncation toward zero succeeds or fails independently of the payload:
`toInt?` is `roundInt` of the finite value. -/
theorem toInt?_value_rz {fmt : Format} (b : Bits fmt) :
    Silmaril.Numeric.Ieee754.Rounding.toInt? .towardZero b.value =
      (value? b.value).map (roundInt .towardZero) := by
  rw [Bits.toInt?_value, Bits.value?_value]

/-- `roundInt` toward zero lies in `[lo, hi]` (with `lo ≤ 0 ≤ hi`) exactly when
the value lies in `(lo - 1, hi + 1)`. -/
theorem roundInt_rz_mem_iff {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (q : ℚ) :
    (lo ≤ roundInt .towardZero q ∧ roundInt .towardZero q ≤ hi) ↔
      ((lo : ℚ) - 1 < q ∧ q < (hi : ℚ) + 1) := by
  simp only [roundInt]
  split
  · rename_i hq
    have h1 : lo ≤ ⌊q⌋ := le_trans hlo (Int.floor_nonneg.mpr hq)
    have h2 : (lo : ℚ) - 1 < q := by
      have : (lo : ℚ) ≤ 0 := by exact_mod_cast hlo
      linarith
    rw [Int.floor_le_iff]
    exact ⟨fun h => ⟨h2, h.2⟩, fun h => ⟨h1, h.2⟩⟩
  · rename_i hq
    have hq' : q < 0 := lt_of_not_ge hq
    have h1 : ⌈q⌉ ≤ hi := le_trans (Int.ceil_le.mpr (by push_cast; linarith)) hhi
    have h2 : q < (hi : ℚ) + 1 := by
      have : (0 : ℚ) ≤ hi := by exact_mod_cast hhi
      linarith
    rw [Int.le_ceil_iff]
    exact ⟨fun h => ⟨h.1, h2⟩, fun h => ⟨h.1, h1⟩⟩

/-- Checked construction succeeds exactly within the format's bounds. -/
theorem ofInt?_isSome_iff (f : IntFormat) (n : ℤ) :
    (Integer.ofInt? f n).isSome ↔ (f.minValue ≤ n ∧ n ≤ f.maxValue) := by
  unfold Integer.ofInt?
  split <;> simp_all

theorem minValue_nonpos (f : IntFormat) : f.minValue ≤ 0 := by
  unfold IntFormat.minValue; split <;> simp

theorem maxValue_nonneg (f : IntFormat) : 0 ≤ f.maxValue := by
  unfold IntFormat.maxValue
  have := f.positive
  split
  · have : (0 : ℤ) < 2 ^ f.width := by positivity
    omega
  · have : (0 : ℤ) < 2 ^ (f.width - 1) := by positivity
    omega

/-- Truncation into `f` succeeds exactly when the extended value lies strictly
between `minValue - 1` and `maxValue + 1`. NaN (sent to `⊥`) and infinities
fail. -/
theorem fromFloat_isSome_iff (f : IntFormat) {fmt : Format} (b : Bits fmt) :
    (Integer.fromFloat? f b.value .towardZero).isSome ↔
      (ofRat (f.minValue - 1) < ext b.value ∧ ext b.value < ofRat (f.maxValue + 1)) := by
  unfold Integer.fromFloat?
  rw [toInt?_value_rz]
  cases hv : value? b.value with
  | none =>
    simp only [Option.map_none, Option.bind_none, Option.isSome_none, Bool.false_eq_true,
      false_iff, not_and, not_lt]
    intro h
    rcases hb : b.value with ⟨s⟩ | _ | ⟨s⟩ | ⟨s, m, e, hm⟩
    · cases s
      · rw [hb] at h; simp [ext] at h
      · simp [ext, ofRat]
    · rw [hb] at h; simp [ext] at h
    · rw [hb] at hv; simp [value?] at hv
    · rw [hb] at hv; simp [value?] at hv
  | some q =>
    obtain ⟨-, he⟩ := value?_eq_some_iff.mp hv
    simp only [Option.map_some, Option.bind_some, he, ofRat_lt_ofRat]
    rw [ofInt?_isSome_iff, roundInt_rz_mem_iff (minValue_nonpos f) (maxValue_nonneg f)]

/-- A successful truncation is `roundInt` toward zero of the finite value. -/
theorem fromFloat_eq_some {f : IntFormat} {fmt : Format} {b : Bits fmt} {r : Integer f}
    (h : Integer.fromFloat? f b.value .towardZero = some r) :
    ∃ q, value? b.value = some q ∧ r.toInt = roundInt .towardZero q := by
  unfold Integer.fromFloat? at h
  rw [toInt?_value_rz] at h
  cases hv : value? b.value with
  | none => rw [hv] at h; cases h
  | some q =>
    rw [hv] at h
    simp only [Option.map_some, Option.bind_some] at h
    exact ⟨q, rfl, Integer.ofInt?_value h⟩

/-! ## Large values are integers -/

/-- A canonical value of magnitude at least `2^(P-1)`, where `P` is the
precision, is an integer: its exponent is nonnegative. -/
theorem isInt_of_large {fmt : Format} (b : Bits fmt) {q : ℚ} (hq : ext b.value = ofRat q)
    (hne : b.isNaN = false) (hbig : (2 : ℚ) ^ (fmt.mantissaBits - 1) ≤ |q|) : ∃ n : ℤ, q = n := by
  have hn := value_normalized b
  rcases hb : b.value with ⟨s⟩ | _ | ⟨s⟩ | ⟨s, m, e, hm⟩
  · rw [hb] at hq; cases s <;> simp [ext, ofRat] at hq
  · exact absurd hb (Bits.value_ne_notANumber hne)
  · rw [hb] at hq; simp only [ext, ofRat_inj] at hq; exact ⟨0, by simp [← hq]⟩
  · rw [hb] at hq hn
    simp only [ext, ofRat_inj] at hq
    have bnd := hn.finite_bounds fmt s m e hm
    by_cases he : 0 ≤ e
    · refine ⟨s.apply m * 2 ^ e.toNat, ?_⟩
      rw [← hq, dyadic]
      push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg he]
    · exfalso
      have habs : |q| = (m : ℚ) * 2 ^ e := by
        rw [← hq, dyadic]; cases s <;> simp [Sign.apply, abs_of_pos (zpow_pos (by norm_num : (0:ℚ) < 2) e)]
      have hm' : (m : ℚ) < 2 ^ fmt.mantissaBits := by exact_mod_cast bnd.2.1
      have hle : (2 : ℚ) ^ e ≤ 1 / 2 := by
        rw [show (1 / 2 : ℚ) = 2 ^ (-1 : ℤ) by norm_num]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hP : 1 ≤ fmt.mantissaBits := by unfold Format.mantissaBits; omega
      have hpow : (2 : ℚ) ^ fmt.mantissaBits = 2 ^ (fmt.mantissaBits - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      have h1 : (m : ℚ) * 2 ^ e ≤ m * (1 / 2) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have h2 : (0 : ℚ) ≤ 2 ^ (fmt.mantissaBits - 1) := by positivity
      linarith

/-- For an integer bound `L ≤ -2^(P-1)`, `L ≤ x` iff `L - 1 < x` on decoded
non-NaN values. -/
theorem le_iff_pred_lt {fmt : Format} (b : Bits fmt) (hne : b.isNaN = false) {L : ℤ}
    (hL : (L : ℚ) ≤ -(2 : ℚ) ^ (fmt.mantissaBits - 1)) :
    ofRat L ≤ ext b.value ↔ ofRat (L - 1) < ext b.value := by
  rcases hb : b.value with ⟨s⟩ | _ | ⟨s⟩ | ⟨s, m, e, hm⟩
  · cases s
    · simp [ext]
    · simp only [ext]
      exact ⟨fun _ => ofRat_lt_top _, fun _ => le_of_lt (ofRat_lt_top _)⟩
  · exact absurd hb (Bits.value_ne_notANumber hne)
  all_goals
    obtain ⟨q, hq⟩ : ∃ q, ext b.value = ofRat q := by rw [hb]; exact ⟨_, rfl⟩
    rw [← hb, hq, ofRat_le_ofRat, ofRat_lt_ofRat]
    constructor
    · intro h; linarith
    · intro h
      by_contra hlt'
      have hlt := lt_of_not_ge hlt'
      have hbig : (2 : ℚ) ^ (fmt.mantissaBits - 1) ≤ |q| := by
        rw [abs_of_neg (by linarith [show (0 : ℚ) ≤ 2 ^ (fmt.mantissaBits - 1) by positivity])]
        linarith
      obtain ⟨n, rfl⟩ := isInt_of_large b hq hne hbig
      have h1 : (L : ℚ) - 1 < n := h
      have h2 : (n : ℚ) < L := hlt
      have h1' : L - 1 < n := by exact_mod_cast h1
      have h2' : n < L := by exact_mod_cast h2
      omega


/-! ## Saturating truncation -/

section Saturating

variable (f : IntFormat) {fmt : Format} (b : Bits fmt)

theorem sat_nan (h : b.isNaN = true) :
    Integer.fromFloatSaturating f b.value .towardZero = Integer.ofIntWrapping f 0 := by
  rw [(Bits.value_eq_notANumber_iff b).mpr h]; rfl

theorem sat_high (h : b.isNaN = false) (hi : ofRat (f.maxValue + 1) ≤ ext b.value) :
    Integer.fromFloatSaturating f b.value .towardZero = Integer.ofIntWrapping f f.maxValue := by
  have hmin := minValue_nonpos f
  have hmax := maxValue_nonneg f
  rcases hb : b.value with ⟨s⟩ | _ | ⟨s⟩ | ⟨s, m, e, hm⟩
  · cases s
    · rw [hb] at hi; simp [ext] at hi
    · rfl
  · exact absurd hb (Bits.value_ne_notANumber h)
  all_goals
    obtain ⟨q, hq⟩ : ∃ q, value? b.value = some q := by rw [hb]; exact ⟨_, rfl⟩
    have he := (value?_eq_some_iff.mp hq).2
    rw [he, ofRat_le_ofRat] at hi
    have hr : Silmaril.Numeric.Ieee754.Rounding.toInt? .towardZero b.value =
        some (roundInt .towardZero q) := by rw [toInt?_value_rz, hq]; rfl
    rw [hb] at hr
    simp only [Integer.fromFloatSaturating, hr, Option.getD_some, Integer.ofIntSaturating]
    have hq0 : (0 : ℚ) ≤ q := by
      have : (0 : ℚ) ≤ f.maxValue := by exact_mod_cast hmax
      linarith
    have hn : f.maxValue + 1 ≤ roundInt .towardZero q := by
      simp only [roundInt, ite_eq_left_iff.mpr (fun h => absurd hq0 h)]
      exact Int.le_floor.mpr (by push_cast; linarith)
    rw [min_eq_left (by omega), max_eq_right (hmin.trans hmax)]

theorem sat_low (h : b.isNaN = false) (lo : ext b.value ≤ ofRat (f.minValue - 1)) :
    Integer.fromFloatSaturating f b.value .towardZero = Integer.ofIntWrapping f f.minValue := by
  have hmin := minValue_nonpos f
  have hmax := maxValue_nonneg f
  rcases hb : b.value with ⟨s⟩ | _ | ⟨s⟩ | ⟨s, m, e, hm⟩
  · cases s
    · rfl
    · rw [hb] at lo; simp only [ext] at lo; exact absurd lo (not_le.mpr (ofRat_lt_top _))
  · exact absurd hb (Bits.value_ne_notANumber h)
  all_goals
    obtain ⟨q, hq⟩ : ∃ q, value? b.value = some q := by rw [hb]; exact ⟨_, rfl⟩
    have he := (value?_eq_some_iff.mp hq).2
    rw [he, ofRat_le_ofRat] at lo
    have hr : Silmaril.Numeric.Ieee754.Rounding.toInt? .towardZero b.value =
        some (roundInt .towardZero q) := by rw [toInt?_value_rz, hq]; rfl
    rw [hb] at hr
    simp only [Integer.fromFloatSaturating, hr, Option.getD_some, Integer.ofIntSaturating]
    have hq0 : q < 0 := by
      have : (f.minValue : ℚ) ≤ 0 := by exact_mod_cast hmin
      linarith
    have hn : roundInt .towardZero q ≤ f.minValue - 1 := by
      simp only [roundInt, ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hq0))]
      exact Int.ceil_le.mpr (by push_cast; linarith)
    rw [min_eq_right (by omega), max_eq_left (by omega)]

end Saturating

end Silmaril.Numeric.Float.Lowering
