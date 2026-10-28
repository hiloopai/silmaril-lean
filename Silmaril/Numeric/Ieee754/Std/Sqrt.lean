module

public import Silmaril.Numeric.Ieee754.Std.Ops
public import Mathlib.Analysis.Real.Sqrt

/-!
# Correctly rounded square root

The exact square root is irrational in general, so its specification lives in
`ℝ`: `exactSqrt` gives the exact outcome (IEEE 754-2019 §5.4.1 squareRoot,
§6.3 `sqrt(-0) = -0`, §7.2(g) invalid for negative operands), delivered by the
real-valued `Deliver`.

The executable `sqrtQ` never forms an irrational number. For an operand `m > 0`
it computes the binade of `√m` from that of `m`, the integer part of
`√m / 2^q` with `Nat.sqrt`, exactness by squaring, and every comparison of the
rounding decision by squaring both sides. `sqrtQ_spec` proves that it delivers
exactly the specified result and flags, for every grid, direction and tininess
detection.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-- Exact outcome of `squareRoot`. -/
noncomputable def exactSqrt : Datum → Exact ℝ
  | .nan s => .nan s
  | .inf false => .inf false false
  | .inf true => .nan true
  | .fin a m => if m = 0 then .num a 0 else if a then .nan true else .num false (Real.sqrt m)

namespace Grid

/-- Executable quantum exponent of `√m`. -/
def sqrtQexp (g : Grid) (m : ℚ) : ℤ := g.clamp (floorLog2 m / 2 - ((g.prec : ℤ) - 1))

/-- Executable rounding of `√m` for a rational `m ≥ 0`. -/
def roundSqrtQ (g : Grid) (mode : RoundingMode) (neg : Bool) (m : ℚ) : ℚ :=
  let q := g.sqrtQexp m
  let t := m / ((2 : ℚ) ^ q) ^ 2
  let n := Nat.sqrt ⌊t⌋₊
  let c : ℕ := if ((n : ℚ)) ^ 2 = t then n else n + 1
  let d : ℚ := n * 2 ^ q
  let u : ℚ := c * 2 ^ q
  pickBy mode neg (4 * m < (d + u) ^ 2) ((d + u) ^ 2 < 4 * m) (n % 2 = 0) d u

theorem floor_sqrt_rat {t : ℚ} (ht : 0 ≤ t) :
    ⌊Real.sqrt (t : ℝ)⌋₊ = Nat.sqrt ⌊t⌋₊ := by
  set n := Nat.sqrt ⌊t⌋₊
  have htr : (0 : ℝ) ≤ t := by exact_mod_cast ht
  rw [Nat.floor_eq_iff (Real.sqrt_nonneg _)]
  constructor
  · rw [Real.le_sqrt (by positivity) htr]
    have h1 : n ^ 2 ≤ ⌊t⌋₊ := Nat.sqrt_le' _
    have h2 : ((⌊t⌋₊ : ℕ) : ℚ) ≤ t := Nat.floor_le ht
    have : ((n : ℚ)) ^ 2 ≤ t := le_trans (by exact_mod_cast h1) h2
    exact_mod_cast this
  · rw [Real.sqrt_lt' (by positivity)]
    have h1 : ⌊t⌋₊ < (n + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have h2 : t < (⌊t⌋₊ : ℚ) + 1 := Nat.lt_floor_add_one t
    have h3 : (⌊t⌋₊ : ℚ) + 1 ≤ ((n + 1 : ℕ) : ℚ) ^ 2 := by exact_mod_cast h1
    have : t < ((n : ℚ) + 1) ^ 2 := by push_cast at h3; linarith
    exact_mod_cast this

theorem ceil_sqrt_rat {t : ℚ} (ht : 0 ≤ t) :
    ⌈Real.sqrt (t : ℝ)⌉₊ =
      (if ((Nat.sqrt ⌊t⌋₊ : ℕ) : ℚ) ^ 2 = t then Nat.sqrt ⌊t⌋₊ else Nat.sqrt ⌊t⌋₊ + 1) := by
  set n := Nat.sqrt ⌊t⌋₊
  have htr : (0 : ℝ) ≤ t := by exact_mod_cast ht
  have hfl := floor_sqrt_rat ht
  have hlo : (n : ℝ) ≤ Real.sqrt t := by
    have := Nat.floor_le (Real.sqrt_nonneg (t : ℝ)); rw [hfl] at this; exact this
  have hhi : Real.sqrt t < n + 1 := by
    have := Nat.lt_floor_add_one (Real.sqrt (t : ℝ)); rw [hfl] at this; exact this
  split_ifs with h
  · have : Real.sqrt (t : ℝ) = n := by
      rw [← h]; push_cast; exact Real.sqrt_sq (by positivity)
    rw [this, Nat.ceil_natCast]
  · rw [Nat.ceil_eq_iff (by omega)]
    push_cast
    refine ⟨?_, hhi.le⟩
    refine lt_of_le_of_ne hlo fun heq => h ?_
    have : ((n : ℝ)) ^ 2 = t := by rw [heq, Real.sq_sqrt htr]
    exact_mod_cast this

theorem sq_lt_sq_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a < b ↔ a ^ 2 < b ^ 2 :=
  (pow_lt_pow_iff_left₀ ha hb (by norm_num)).symm

theorem roundSqrtQ_spec (g : Grid) (hp : 1 ≤ g.prec) (mode : RoundingMode) (neg : Bool)
    {m : ℚ} (hm : 0 ≤ m) :
    g.RoundMag mode neg (Real.sqrt (m : ℝ)) ((g.roundSqrtQ mode neg m : ℚ) : ℝ) := by
  have hmr : (0 : ℝ) ≤ m := by exact_mod_cast hm
  rcases hm.lt_or_eq with hm' | rfl
  · set y := Real.sqrt (m : ℝ) with hy
    have hypos : 0 < y := Real.sqrt_pos.mpr (by exact_mod_cast hm')
    -- the binade of √m
    set Lm := floorLog2 m
    have hLm : Lm = Int.log 2 m := floorLog2_eq hm'
    have hlow : (2 : ℚ) ^ Lm ≤ m := by rw [hLm]; exact two_zpow_log_le hm'
    have hhigh : m < (2 : ℚ) ^ (Lm + 1) := by rw [hLm]; exact lt_two_zpow_log_succ m
    have hlowR : (2 : ℝ) ^ Lm ≤ m := by
      have h : ((2 ^ Lm : ℚ) : ℝ) ≤ (m : ℝ) := Rat.cast_le.mpr hlow
      simpa using h
    have hhighR : (m : ℝ) < (2 : ℝ) ^ (Lm + 1) := by
      have h : (m : ℝ) < ((2 ^ (Lm + 1) : ℚ) : ℝ) := Rat.cast_lt.mpr hhigh
      simpa using h
    have hlog : Int.log 2 y = Lm / 2 := by
      apply log_eq_of_bounds hypos
      · rw [hy, Real.le_sqrt (by positivity) hmr, ← zpow_natCast, ← zpow_mul]
        refine le_trans (zpow_le_zpow_right₀ (by norm_num) ?_) hlowR
        push_cast
        omega
      · rw [hy, Real.sqrt_lt' (by positivity), ← zpow_natCast, ← zpow_mul]
        refine lt_of_lt_of_le hhighR (zpow_le_zpow_right₀ (by norm_num) ?_)
        push_cast
        omega
    have hq : g.qexp y = g.sqrtQexp m := by
      simp only [qexp, sqrtQexp, hlog]
      rfl
    set q := g.sqrtQexp m
    set t : ℚ := m / ((2 : ℚ) ^ q) ^ 2 with ht
    have ht0 : 0 ≤ t := by positivity
    have hpos : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) _
    have hscale : y / (2 : ℝ) ^ q = Real.sqrt (t : ℝ) := by
      rw [ht]
      push_cast
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hpos.le]
    have key := g.roundMag_floor_ceil hp mode neg (le_of_lt hypos)
    rw [hq, hscale, floor_sqrt_rat ht0, ceil_sqrt_rat ht0] at key
    convert key using 1
    simp only [roundSqrtQ]
    rw [pickBy_map (fun r : ℚ => (r : ℝ))]
    unfold pick
    set n := Nat.sqrt ⌊t⌋₊
    set c : ℕ := if ((n : ℚ)) ^ 2 = t then n else n + 1
    have hd : (((n : ℚ) * 2 ^ q : ℚ) : ℝ) = (n : ℝ) * 2 ^ q := by push_cast; rfl
    have hu : (((c : ℚ) * 2 ^ q : ℚ) : ℝ) = (c : ℝ) * 2 ^ q := by push_cast; rfl
    rw [hd, hu]
    have hy2 : (2 * y) ^ 2 = 4 * (m : ℝ) := by
      rw [mul_pow, hy, Real.sq_sqrt hmr]; norm_num
    have hdu : (0 : ℝ) ≤ (n : ℝ) * 2 ^ q + (c : ℝ) * 2 ^ q := by positivity
    apply pickBy_congr
    · rw [show y - (n : ℝ) * 2 ^ q < (c : ℝ) * 2 ^ q - y ↔
          2 * y < (n : ℝ) * 2 ^ q + (c : ℝ) * 2 ^ q by constructor <;> intro h <;> linarith]
      rw [sq_lt_sq_iff_of_nonneg (by positivity) hdu, hy2]
      constructor <;> intro h
      · have : ((4 * m : ℚ) : ℝ) < (((n : ℚ) * 2 ^ q + (c : ℚ) * 2 ^ q) ^ 2 : ℚ) := by
          exact_mod_cast h
        push_cast at this; exact this
      · have : (((4 * m : ℚ)) : ℝ) < (((n : ℚ) * 2 ^ q + (c : ℚ) * 2 ^ q) ^ 2 : ℚ) := by
          push_cast; exact h
        exact_mod_cast this
    · rw [show (c : ℝ) * 2 ^ q - y < y - (n : ℝ) * 2 ^ q ↔
          (n : ℝ) * 2 ^ q + (c : ℝ) * 2 ^ q < 2 * y by constructor <;> intro h <;> linarith]
      rw [sq_lt_sq_iff_of_nonneg hdu (by positivity), hy2]
      constructor <;> intro h
      · have : ((((n : ℚ) * 2 ^ q + (c : ℚ) * 2 ^ q) ^ 2 : ℚ) : ℝ) < ((4 * m : ℚ) : ℝ) := by
          exact_mod_cast h
        push_cast at this; exact this
      · have : ((((n : ℚ) * 2 ^ q + (c : ℚ) * 2 ^ q) ^ 2 : ℚ) : ℝ) < ((4 * m : ℚ) : ℝ) := by
          push_cast; exact h
        exact_mod_cast this
    · exact Iff.rfl
  · have h0 : g.roundSqrtQ mode neg 0 = 0 := by
      simp [roundSqrtQ, pickBy_self]
    rw [h0]
    simp only [Rat.cast_zero, Real.sqrt_zero]
    refine ⟨0, 0, g.isDown_zero, g.isUp_zero, ?_⟩
    simp [pick_self]

end Grid

/-- Tininess of `√m` from the square, with unbounded-exponent rounding `ru`. -/
def TinySq (f : BinFormat) (tin : TininessDetection) (m : ℚ) (ru : ℚ) : Bool :=
  match tin with
  | .beforeRounding => decide (m < ((2 : ℚ) ^ f.emin) ^ 2)
  | .afterRounding => decide (ru < (2 : ℚ) ^ f.emin)

/-- Executable square root at the value level. -/
def sqrtQ (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) : Datum → Datum × Flags
  | .nan s => (.nan false, { invalidOperation := s })
  | .inf false => (.inf false, {})
  | .inf true => (.nan false, { invalidOperation := true })
  | .fin a m =>
    if m = 0 then (.fin a 0, {}) else if a then (.nan false, { invalidOperation := true }) else
    let r := f.grid.roundSqrtQ mode false m
    let ru := f.gridUnbounded.roundSqrtQ mode false m
    ((if f.maxFinite < r then overflowResult f mode false else .fin false r),
      { overflow := decide (f.maxFinite < r)
        inexact := decide (f.maxFinite < r ∨ r ^ 2 ≠ m)
        underflow := TinySq f tin m ru && decide (r ^ 2 ≠ m) })

theorem BinFormat.maxFinite_pos (f : BinFormat) : 0 < f.maxFinite := by
  unfold BinFormat.maxFinite
  have : (1 : ℚ) < 2 ^ f.prec := one_lt_pow₀ (by norm_num) (by have := f.two_le_prec; omega)
  have : (0 : ℚ) < 2 ^ f.prec - 1 := by linarith
  positivity

theorem roundSpec_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
    (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) (neg : Bool) :
    RoundSpec f tin mode neg (0 : K) (.fin neg 0) {} := by
  refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
  · exact ⟨0, 0, Grid.isDown_zero _, Grid.isUp_zero _, by simp [pick_self]⟩
  · exact ⟨0, 0, Grid.isDown_zero _, Grid.isUp_zero _, by simp [pick_self]⟩
  · simp [not_lt.mpr f.maxFinite_pos.le]
  · simp [not_lt.mpr f.maxFinite_pos.le]

theorem rat_cast_eq_sqrt_iff {r m : ℚ} (hr : 0 ≤ r) (hm : 0 ≤ m) :
    (r : ℝ) = Real.sqrt (m : ℝ) ↔ r ^ 2 = m := by
  constructor
  · intro h
    have : ((r : ℝ)) ^ 2 = m := by rw [h, Real.sq_sqrt (by exact_mod_cast hm)]
    exact_mod_cast this
  · intro h
    rw [← h]
    push_cast
    rw [Real.sqrt_sq (by exact_mod_cast hr)]

/-- The executable square root delivers exactly the specified result and flags. -/
theorem sqrtQ_spec (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) (x : Datum)
    (hx : ∀ a m, x = .fin a m → 0 ≤ m) :
    Deliver f tin mode (exactSqrt x) (sqrtQ f tin mode x).1 (sqrtQ f tin mode x).2 := by
  match x with
  | .nan s => exact ⟨rfl, rfl⟩
  | .inf false => exact ⟨rfl, rfl⟩
  | .inf true => exact ⟨rfl, rfl⟩
  | .fin a m =>
    have hm := hx a m rfl
    simp only [exactSqrt, sqrtQ]
    by_cases h0 : m = 0
    · simp only [h0, ite_true]
      simp only [Deliver, abs_zero]
      exact roundSpec_zero f tin mode a
    · simp only [h0, ite_false]
      cases a
      · simp only [Bool.false_eq_true, ite_false, Deliver]
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        set r := f.grid.roundSqrtQ mode false m
        set ru := f.gridUnbounded.roundSqrtQ mode false m
        have hr := f.grid.roundSqrtQ_spec f.one_le_prec mode false hm
        have hru := f.gridUnbounded.roundSqrtQ_spec f.one_le_prec mode false hm
        have hr0 : 0 ≤ r := by exact_mod_cast Grid.rep_nonneg hr.rep
        have hru0 : 0 ≤ ru := by exact_mod_cast Grid.rep_nonneg hru.rep
        refine ⟨r, ru, hr, hru, rfl, ?_⟩
        have hne : ((r : ℝ) ≠ Real.sqrt m) ↔ r ^ 2 ≠ m := (rat_cast_eq_sqrt_iff hr0 hm).not
        have hsq0 : Real.sqrt (m : ℝ) ≠ 0 := by
          rw [Real.sqrt_ne_zero']; exact_mod_cast lt_of_le_of_ne hm (Ne.symm h0)
        have htiny : (TinySq f tin m ru = true) ↔ Tiny f tin (Real.sqrt (m : ℝ)) ru := by
          cases tin
          · simp only [TinySq, Tiny, decide_eq_true_eq]
            rw [Real.sqrt_lt' (by positivity)]
            have hc : ((((2 : ℚ) ^ f.emin) ^ 2 : ℚ) : ℝ) = ((2 : ℝ) ^ f.emin) ^ 2 := by push_cast; rfl
            rw [← hc, Rat.cast_lt]
          · simp only [TinySq, Tiny, decide_eq_true_eq]
            have hc : (((2 : ℚ) ^ f.emin : ℚ) : ℝ) = (2 : ℝ) ^ f.emin := by push_cast; rfl
            rw [← hc, Rat.cast_lt]
        simp only [Flags.mk.injEq, true_and]
        refine ⟨?_, ?_⟩
        · rw [Bool.eq_iff_iff]
          simp only [Bool.and_eq_true, decide_eq_true_eq, htiny]
          rw [hne]
          exact ⟨fun ⟨h1, h2⟩ => ⟨hsq0, h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩
        · exact decide_eq_decide.mpr (or_congr Iff.rfl hne.symm)
      · simp only [ite_true]
        exact ⟨rfl, rfl⟩

end Silmaril.Numeric.Ieee754.Std
