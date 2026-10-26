module

public import Silmaril.Numeric.Ieee754.Flags.Executable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Agreement of division and square root with the delivered result

`Silmaril.Numeric.Ieee754.Flags.Executable` shows that the executable rounding
`Rounding.packRounded` delivers `deliver` of the exact value. Division and
square root do not go through `packRounded`: `Rounding.divRounded` and
`Rounding.sqrtRounded` first compute a truncated quotient or integer square root
with a residual (`divCore`, `sqrtCore`) and then round it with
`roundWithAccuracy`. This module proves that they deliver the same result as the
specification:

* `roundedOf?_unpack_divRounded`: for finite operands of values `a` and `b ≠ 0`,
  the decoded quotient is `deliver f mode (a / b)`;
* `roundedOf?_unpack_sqrtRounded`: for a finite operand of value `a ≥ 0`, the
  decoded root, read in `ℝ`, is `deliver f mode (Real.sqrt a)`.

The shared step (`targetExponent_eq_quantum_of_floor`) is that a significand
truncated on a grid no coarser than the destination's selects the
specification's `quantum` as its rounding grid. With these, the inexact flag of
binary32/binary64 division and square root holds exactly when the returned
value differs from the exact result (`F32.divFlags_inexact_iff`,
`F32.sqrtFlags_inexact_iff` and the binary64 versions).
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model Float.Model.UnpackedFloat Conformance

/-! ## The grid of a truncated significand -/

section Grid

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

omit [IsStrictOrderedRing K] in
/-- The specification's grid exponent in the executable's terms. -/
theorem quantum_eq_targetExponent (f : Format) (x : K) :
    quantum f x = f.targetExponent (leadingExponent x + 1) := by
  have hmin := minQuantum_eq_minExponent f
  unfold minQuantum at hmin
  unfold quantum Format.targetExponent precision at *
  omega

theorem targetExponent_mono (f : Format) {s t : ℤ} (h : s ≤ t) :
    f.targetExponent s ≤ f.targetExponent t := by
  unfold Format.targetExponent
  omega

omit [IsStrictOrderedRing K] in
theorem quantum_neg (f : Format) (x : K) : quantum f (-x) = quantum f x := by
  simp [quantum, leadingExponent]

/-- A significand `m` with `m * 2 ^ E ≤ x < (m + 1) * 2 ^ E`, on a grid `E` no
coarser than the specification's, satisfies the precondition of
`roundWithAccuracy`, and the executable then rounds on the grid `quantum f x`. -/
theorem targetExponent_eq_quantum_of_floor (f : Format) {x : K} (hx : 0 < x) {m : ℕ} {E : ℤ}
    (hlo : (m : K) * 2 ^ E ≤ x) (hhi : x < ((m : K) + 1) * 2 ^ E)
    (hE : E ≤ f.targetExponent (leadingExponent x + 1)) :
    E ≤ f.targetExponent (totalExponent m E) ∧
      f.targetExponent (totalExponent m E) = quantum f x := by
  rw [quantum_eq_targetExponent]
  have hp := two_le_precision f
  unfold precision at hp
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    have hlt : leadingExponent x < E := by
      apply leadingExponent_lt hx.ne'
      rw [abs_of_pos hx]
      simpa using hhi
    unfold totalExponent Format.targetExponent at *
    simp only [Nat.log2_zero, CharP.cast_eq_zero, zero_add] at *
    omega
  · have hL : leadingExponent x = (m.log2 : ℤ) + E := by
      apply leadingExponent_eq
      · rw [abs_of_pos hx]
        refine le_trans ?_ hlo
        rw [zpow_add₀ (by norm_num : (2 : K) ≠ 0), zpow_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hm))
          (two_zpow_pos E).le
      · rw [abs_of_pos hx]
        refine lt_of_lt_of_le hhi ?_
        rw [show (m.log2 : ℤ) + E + 1 = ((m.log2 + 1 : ℕ) : ℤ) + E by push_cast; ring,
          zpow_add₀ (by norm_num : (2 : K) ≠ 0), zpow_natCast]
        have h1 : m + 1 ≤ 2 ^ (m.log2 + 1) := Nat.lt_log2_self
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (two_zpow_pos E).le
    rw [hL] at hE ⊢
    unfold totalExponent
    constructor
    · convert hE using 2
      ring
    · congr 1
      ring

/-- A significand certificate on the grid `quantum f x` gives the value
`roundGradual` of the signed magnitude. -/
theorem roundGradual_of_roundsOnGrid (f : Format) (mode : RoundingMode) (sign : Sign) {x : K}
    (hx : 0 ≤ x) {r : UnpackedFloat} (h : RoundsOnGrid mode sign x (quantum f x) r) :
    ∃ w : ℚ, value? r = some w ∧
      (w : K) = roundGradual f mode (if sign = .negative then -x else x) := by
  obtain ⟨n, hm, hv⟩ := h
  refine ⟨_, hv, ?_⟩
  have hq : quantum f (if sign = .negative then -x else x) = quantum f x := by
    split <;> simp [quantum_neg]
  have hsplit : (if sign = .negative then -x else x) / 2 ^ quantum f x =
      if sign = .negative then -(x / 2 ^ quantum f x) else x / 2 ^ quantum f x := by
    split <;> simp [neg_div]
  have hpos : 0 ≤ x / 2 ^ quantum f x := div_nonneg hx (two_zpow_pos _).le
  unfold roundGradual roundAt
  rw [hq, hsplit, roundInt_of_mantissaRounds mode sign hpos hm]
  simp [dyadic]

end Grid

/-! ## Packing a rounded value -/

/-- Reading a delivered rational result in another ordered field. -/
def Rounded.cast {K : Type*} [RatCast K] : Rounded ℚ → Rounded K
  | .finite v => .finite (v : K)
  | .infinite negative => .infinite negative

@[simp] theorem Rounded.cast_rat (r : Rounded ℚ) : Rounded.cast r = r := by
  cases r <;> simp [Rounded.cast]

section Pack

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

private theorem overflowToInfinity_eq' (mode : RoundingMode) (sign : Sign) :
    Rounding.overflowToInfinity mode sign =
      overflowsToInfinity mode (decide (sign = .negative)) := by
  cases mode <;> cases sign <;> rfl

/-- Packing a canonical unpacked value whose rational value is `roundGradual`
of an exact result `x` (in any ordered field) delivers `deliver` of `x`,
including the overflow result, provided a finite value carries the sign of `x`. -/
theorem roundedOf?_unpack_packNormalized (f : Format) (mode : RoundingMode) {r : UnpackedFloat}
    {x : K} {w : ℚ} (hr : value? r = some w) (hw : (w : K) = roundGradual f mode x)
    (hnorm : ExponentNormalized f r)
    (hsign : ∀ s m E hm, r = .finite s m E hm → (s = .negative ↔ x < 0)) :
    (roundedOf? (UnpackedFloat.unpack f (Rounding.packNormalized f mode r))).map Rounded.cast =
      some (deliver f mode x) := by
  have habs : |(w : K)| ≤ maxFinite f ↔ |w| ≤ maxFinite f := by
    rw [← maxFinite_ratCast (L := K) f, ← Rat.cast_abs, Rat.cast_le]
  by_cases ho : Overflows f mode x
  · have hbig : maxFinite f < |w| := by
      rw [← not_le, ← habs, hw, abs_roundGradual_le_iff]
      exact not_not.mpr ho
    cases r with
    | notANumber => simp [value?] at hr
    | infinity s => simp [value?] at hr
    | zero s =>
      simp only [value?, Option.some.injEq] at hr
      subst hr
      simp only [abs_zero] at hbig
      exact absurd hbig (not_lt.mpr (maxFinite_pos f).le)
    | finite s m E hm =>
      simp only [value?, Option.some.injEq] at hr
      have hover : ¬ NoExponentOverflow f (.finite s m E hm) := by
        rw [noExponentOverflow_iff f s hm hnorm, hr]
        exact not_le.mpr hbig
      have hover' : 2 ^ f.exponentBits ≤
          (E + f.exponentBias + f.mantissaBitsWithoutImplicit).toNat + 1 := by
        change ¬ ((E + f.exponentBias + f.mantissaBitsWithoutImplicit).toNat <
          2 ^ f.exponentBits - 1) at hover
        omega
      rw [unpack_packNormalized_overflow f mode s m E hm hover']
      have hneg := hsign s m E hm rfl
      unfold deliver
      simp only [ho, ↓reduceIte, overflowToInfinity_eq', decide_eq_decide.mpr hneg]
      split
      · simp [roundedOf?, Rounded.cast, hneg]
      · have hl := value?_largestFinite f s
        cases hlf : largestFinite f s with
        | finite s'' m' e' hm' =>
          rw [hlf] at hl
          simp only [roundedOf?, value?, Option.some.injEq, Option.map_some, Rounded.cast] at hl ⊢
          rw [hl]
          by_cases hs : s = .negative
          · simp [hs, hneg.mp hs, maxFinite_ratCast]
          · have : ¬ x < 0 := fun h => hs (hneg.mpr h)
            simp [hs, this, maxFinite_ratCast]
        | _ => simp [largestFinite] at hlf
  · have hle : |w| ≤ maxFinite f := by
      rw [← habs, hw, abs_roundGradual_le_iff]
      exact ho
    have hin : NoExponentOverflow f r := by
      cases r with
      | finite s m E hm =>
        rw [noExponentOverflow_iff f s hm hnorm]
        simp only [value?, Option.some.injEq] at hr
        rw [hr]
        exact hle
      | _ => trivial
    rw [unpack_packNormalized f mode r hnorm hin, deliver_of_not_overflows ho,
      (roundedOf?_eq_finite_iff r w).mpr hr]
    simp [Rounded.cast, hw]

end Pack

/-! ## Division -/

private theorem sign_div_apply (left right : Sign) (n d : ℕ) (en ed : ℤ) :
    dyadic (left.apply n) en / dyadic (right.apply d) ed =
      if left / right = .negative then -((n : ℚ) * 2 ^ en / ((d : ℚ) * 2 ^ ed))
      else (n : ℚ) * 2 ^ en / ((d : ℚ) * 2 ^ ed) := by
  have hpp : Sign.positive / Sign.positive = .positive := rfl
  have hpn : Sign.positive / Sign.negative = .negative := rfl
  have hnp : Sign.negative / Sign.positive = .negative := rfl
  have hnn : Sign.negative / Sign.negative = .positive := rfl
  cases left <;> cases right <;>
    simp [dyadic, Sign.apply, neg_div, div_neg, hpp, hpn, hnp, hnn]

private theorem div_neg_iff (left right : Sign) {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (en ed : ℤ) :
    left / right = .negative ↔ dyadic (left.apply n) en / dyadic (right.apply d) ed < 0 := by
  rw [sign_div_apply]
  have hpos : (0 : ℚ) < (n : ℚ) * 2 ^ en / ((d : ℚ) * 2 ^ ed) := by
    have : (0 : ℚ) < n := by exact_mod_cast hn
    have : (0 : ℚ) < d := by exact_mod_cast hd
    positivity
  split
  · simp_all
  · simp_all [not_lt.mpr hpos.le]

/-- The executable division of two finite operands delivers `deliver` of the
exact quotient, for every rounding direction. -/
theorem roundedOf?_unpack_divRounded (f : Format) (mode : RoundingMode) {x y : UnpackedFloat}
    {a b : ℚ} (hx : value? x = some a) (hy : value? y = some b) (hb : b ≠ 0) :
    roundedOf? (UnpackedFloat.unpack f (Rounding.divRounded f mode x y)) =
      some (deliver f mode (a / b)) := by
  cases y with
  | notANumber => simp [value?] at hy
  | infinity _ => simp [value?] at hy
  | zero _ =>
    simp only [value?, Option.some.injEq] at hy
    exact absurd hy.symm hb
  | finite right d ed hd =>
  cases x with
  | notANumber => simp [value?] at hx
  | infinity _ => simp [value?] at hx
  | zero left =>
    simp only [value?, Option.some.injEq] at hx
    subst hx
    have hz : Rounding.divRounded f mode (.zero left) (.finite right d ed hd) =
        Rounding.packNormalized f mode (.zero (left / right)) := rfl
    rw [hz, unpack_packNormalized f mode (.zero (left / right)) trivial trivial, zero_div,
      deliver_of_representable f mode (representable_zero f)]
    rfl
  | finite left n en hn =>
    simp only [value?, Option.some.injEq] at hx hy
    subst hx hy
    set q : ℚ := (n : ℚ) * 2 ^ en / ((d : ℚ) * 2 ^ ed) with hqdef
    have hq : 0 < q := by
      have : (0 : ℚ) < n := by exact_mod_cast hn
      have : (0 : ℚ) < d := by exact_mod_cast hd
      positivity
    set core := divCore f n en d ed with hcore
    have hdiv : Rounding.divRounded f mode (.finite left n en hn) (.finite right d ed hd) =
        Rounding.packNormalized f mode
          (Rounding.roundWithAccuracy f mode (left / right) core.1 core.2.1 core.2.2) := rfl
    -- The core's significand is the quotient truncated on its grid.
    have hshift : (0 : ℤ) ≤ en - ed - core.2.1 := by
      simp only [hcore, divCore]
      omega
    have hscale : q / 2 ^ core.2.1 = ((n * 2 ^ (en - ed - core.2.1).toNat : ℕ) : ℚ) / d := by
      rw [hqdef]
      push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg hshift]
      rw [show en - ed - core.2.1 = en - (ed + core.2.1) by ring,
        zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      field_simp
    have hm : core.1 = (n * 2 ^ (en - ed - core.2.1).toNat) / d := by
      simp only [hcore, divCore, Nat.shiftLeft_eq]
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have hlo : (core.1 : ℚ) * 2 ^ core.2.1 ≤ q := by
      rw [← le_div_iff₀ (two_zpow_pos _), hscale, hm, le_div_iff₀ hdq]
      exact_mod_cast Nat.div_mul_le_self _ _
    have hhi : q < ((core.1 : ℚ) + 1) * 2 ^ core.2.1 := by
      rw [← div_lt_iff₀ (two_zpow_pos _), hscale, hm, div_lt_iff₀ hdq]
      have := Nat.lt_mul_div_succ (n * 2 ^ (en - ed - core.2.1).toNat) hd
      rw [Nat.mul_comm d] at this
      exact_mod_cast this
    -- The core's grid is no coarser than the specification's.
    have hE : core.2.1 ≤ f.targetExponent (leadingExponent q + 1) := by
      have hT : core.2.1 ≤ f.targetExponent (totalExponent n en - totalExponent d ed) := by
        simp only [hcore, divCore]
        omega
      refine le_trans hT (targetExponent_mono f ?_)
      have hA : (n.log2 : ℤ) + en - ((d.log2 : ℤ) + 1 + ed) ≤ leadingExponent q := by
        apply le_leadingExponent
        rw [abs_of_pos hq, hqdef, le_div_iff₀ (by positivity)]
        have h1 : (d : ℚ) ≤ 2 ^ ((d.log2 : ℤ) + 1) := by
          have : d < 2 ^ (d.log2 + 1) := Nat.lt_log2_self
          rw [show ((d.log2 : ℤ) + 1) = ((d.log2 + 1 : ℕ) : ℤ) by push_cast; ring,
            zpow_natCast]
          exact_mod_cast this.le
        have h2 : (2 : ℚ) ^ (n.log2 : ℤ) ≤ n := by
          rw [zpow_natCast]
          exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hn)
        have h3 : (2 : ℚ) ^ ((n.log2 : ℤ) + en - ((d.log2 : ℤ) + 1 + ed)) *
            (2 ^ ((d.log2 : ℤ) + 1) * 2 ^ ed) = 2 ^ (n.log2 : ℤ) * 2 ^ en := by
          have h2ne : (2 : ℚ) ≠ 0 := by norm_num
          rw [← zpow_add₀ h2ne, ← zpow_add₀ h2ne, ← zpow_add₀ h2ne]
          congr 1
          ring
        calc (2 : ℚ) ^ ((n.log2 : ℤ) + en - ((d.log2 : ℤ) + 1 + ed)) * ((d : ℚ) * 2 ^ ed)
            ≤ 2 ^ ((n.log2 : ℤ) + en - ((d.log2 : ℤ) + 1 + ed)) *
                (2 ^ ((d.log2 : ℤ) + 1) * 2 ^ ed) := by
              apply mul_le_mul_of_nonneg_left _ (two_zpow_pos _).le
              exact mul_le_mul_of_nonneg_right h1 (two_zpow_pos _).le
          _ = 2 ^ (n.log2 : ℤ) * 2 ^ en := h3
          _ ≤ n * 2 ^ en := mul_le_mul_of_nonneg_right h2 (two_zpow_pos _).le
      unfold totalExponent
      omega
    obtain ⟨hE1, hG⟩ := targetExponent_eq_quantum_of_floor f hq hlo hhi hE
    have hgrid := divCore_rounding_correct (K := ℚ) f mode (left / right) n d en ed hd
    simp only [← hcore] at hgrid
    rw [shiftToTargetExponent_exponent_eq f _ _ _ hE1, hG] at hgrid
    obtain ⟨w, hw, hwv⟩ := roundGradual_of_roundsOnGrid f mode (left / right) hq.le hgrid
    rw [hqdef, ← sign_div_apply] at hwv
    have hsign : ∀ s m E hm,
        Rounding.roundWithAccuracy f mode (left / right) core.1 core.2.1 core.2.2 =
          .finite s m E hm →
        (s = .negative ↔ dyadic (left.apply n) en / dyadic (right.apply d) ed < 0) := by
      intro s m E hm h
      have : s = left / right := by
        simp only [Rounding.roundWithAccuracy] at h
        split at h
        · cases h
        · cases h
          rfl
      rw [this]
      exact div_neg_iff left right hn hd en ed
    have := roundedOf?_unpack_packNormalized (K := ℚ) f mode hw hwv
      (roundWithAccuracy_normalized f mode _ _ _ _ hE1) hsign
    rw [hdiv]
    simpa using this

/-! ## Square root -/

/-- The executable square root of a finite nonnegative operand, read in `ℝ`,
delivers `deliver` of the real square root, for every rounding direction. -/
theorem roundedOf?_unpack_sqrtRounded (f : Format) (mode : RoundingMode) {x : UnpackedFloat}
    {a : ℚ} (hx : value? x = some a) (ha : 0 ≤ a) :
    (roundedOf? (UnpackedFloat.unpack f (Rounding.sqrtRounded f mode x))).map Rounded.cast =
      some (deliver f mode (Real.sqrt (a : ℝ))) := by
  cases x with
  | notANumber => simp [value?] at hx
  | infinity _ => simp [value?] at hx
  | zero s =>
    simp only [value?, Option.some.injEq] at hx
    subst hx
    have hz : Rounding.sqrtRounded f mode (.zero s) =
        Rounding.packNormalized f mode (.zero s) := rfl
    rw [hz, unpack_packNormalized f mode (.zero s) trivial trivial, Rat.cast_zero, Real.sqrt_zero,
      deliver_of_representable f mode (representable_zero f)]
    simp [roundedOf?, Rounded.cast]
  | finite sign n e hn =>
    simp only [value?, Option.some.injEq] at hx
    subst hx
    cases sign with
    | negative =>
      have : dyadic (Sign.negative.apply n) e < 0 := by
        have : (0 : ℚ) < n := by exact_mod_cast hn
        have := two_zpow_pos (K := ℚ) e
        simp only [dyadic, Sign.apply, Int.cast_neg, Int.cast_natCast]
        nlinarith
      exact absurd ha (not_le.mpr this)
    | positive =>
    have hval : ((dyadic (Sign.positive.apply n) e : ℚ) : ℝ) = (n : ℝ) * 2 ^ e := by
      simp [dyadic, Sign.apply]
    rw [hval]
    set x : ℝ := Real.sqrt ((n : ℝ) * 2 ^ e) with hxdef
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hx : 0 < x := Real.sqrt_pos.mpr (by positivity)
    set core := sqrtCore f n e with hcore
    have hsq : Rounding.sqrtRounded f mode (.finite .positive n e hn) =
        Rounding.packNormalized f mode
          (Rounding.roundWithAccuracy f mode .positive core.1 core.2.1 core.2.2) := rfl
    have hE2 : core.2.1 ≤ e / 2 := min_le_left _ _
    have hshift : (0 : ℤ) ≤ e - 2 * core.2.1 := by omega
    -- The root is the integer square root of the operand scaled to the grid.
    set N : ℕ := n * 2 ^ (e - 2 * core.2.1).toNat with hN
    have hroot : core.1 = Nat.sqrt N := by
      simp only [hcore, sqrtCore, Nat.shiftLeft_eq, hN]
    have hscale : x = Real.sqrt (N : ℝ) * 2 ^ core.2.1 := by
      have hsplit : (n : ℝ) * 2 ^ e = (N : ℝ) * (2 ^ core.2.1) ^ 2 := by
        rw [hN]
        push_cast
        rw [← zpow_natCast (2 : ℝ), Int.toNat_of_nonneg hshift, ← zpow_natCast, ← zpow_mul,
          mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 2
        push_cast
        ring
      rw [hxdef, hsplit, Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (two_zpow_pos _).le]
    have hlo : (core.1 : ℝ) * 2 ^ core.2.1 ≤ x := by
      rw [hscale, hroot]
      exact mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt (two_zpow_pos _).le
    have hhi : x < ((core.1 : ℝ) + 1) * 2 ^ core.2.1 := by
      rw [hscale, hroot]
      exact mul_lt_mul_of_pos_right Real.real_sqrt_lt_nat_sqrt_succ (two_zpow_pos _)
    -- The core's grid is no coarser than the specification's.
    have hE : core.2.1 ≤ f.targetExponent (leadingExponent x + 1) := by
      have hT : core.2.1 ≤ f.targetExponent ((totalExponent n e + 1) / 2) := min_le_right _ _
      refine le_trans hT (targetExponent_mono f ?_)
      set k : ℤ := ((n.log2 : ℤ) + e) / 2 with hk
      have hA : k ≤ leadingExponent x := by
        apply le_leadingExponent
        rw [abs_of_pos hx, hxdef, Real.le_sqrt (two_zpow_pos _).le (by positivity),
          ← zpow_natCast,
          ← zpow_mul]
        have h2 : (2 : ℝ) ^ (n.log2 : ℤ) ≤ n := by
          rw [zpow_natCast]
          exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hn)
        calc (2 : ℝ) ^ (k * ((2 : ℕ) : ℤ)) ≤ 2 ^ ((n.log2 : ℤ) + e) :=
              zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
          _ = 2 ^ (n.log2 : ℤ) * 2 ^ e := zpow_add₀ (by norm_num) _ _
          _ ≤ n * 2 ^ e := mul_le_mul_of_nonneg_right h2 (two_zpow_pos _).le
      unfold totalExponent
      omega
    obtain ⟨hE1, hG⟩ := targetExponent_eq_quantum_of_floor f hx hlo hhi hE
    have hgrid := sqrtCore_rounding_correct f mode n e
    simp only [← hcore, ← hxdef] at hgrid
    rw [shiftToTargetExponent_exponent_eq f _ _ _ hE1, hG] at hgrid
    obtain ⟨w, hw, hwv⟩ := roundGradual_of_roundsOnGrid f mode .positive hx.le hgrid
    simp only [reduceCtorEq, ↓reduceIte] at hwv
    have hsign : ∀ s m E hm,
        Rounding.roundWithAccuracy f mode .positive core.1 core.2.1 core.2.2 = .finite s m E hm →
        (s = .negative ↔ x < 0) := by
      intro s m E hm h
      have : s = .positive := by
        simp only [Rounding.roundWithAccuracy] at h
        split at h
        · cases h
        · cases h
          rfl
      subst this
      simp [not_lt.mpr hx.le]
    rw [hsq]
    exact roundedOf?_unpack_packNormalized (K := ℝ) f mode hw hwv
      (roundWithAccuracy_normalized f mode _ _ _ _ hE1) hsign

/-- Inexact over `ℝ` in terms of a delivered rational result. -/
theorem inexact_iff_of_map_cast (f : Format) (mode : RoundingMode) {r : Option (Rounded ℚ)}
    {x : ℝ} (h : r.map Rounded.cast = some (deliver f mode x)) :
    Inexact f mode x ↔ ¬ ∃ v : ℚ, r = some (.finite v) ∧ (v : ℝ) = x := by
  unfold Inexact
  constructor
  · rintro hne ⟨v, rfl, hv⟩
    simp only [Option.map_some, Rounded.cast, Option.some.injEq] at h
    exact hne (by rw [← h, hv])
  · intro hno heq
    rw [heq] at h
    cases r with
    | none => simp at h
    | some r0 =>
      cases r0 with
      | finite v =>
        simp only [Option.map_some, Rounded.cast, Option.some.injEq, Rounded.finite.injEq] at h
        exact hno ⟨v, rfl, h⟩
      | infinite n => simp [Rounded.cast] at h

end Silmaril.Numeric.Ieee754.FlagSpec

/-! ## Binary32 and binary64 -/

namespace Silmaril.Numeric.Ieee754

open Float.Model Float.Model.UnpackedFloat Conformance FlagSpec

namespace F32

theorem divWith_rounded? (mode : RoundingMode) {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hb : b ≠ 0) :
    (divWith mode x y).rounded? = some (deliver .binary32 mode (a / b)) :=
  roundedOf?_unpack_divRounded .binary32 mode ((value?_model_unpack32 x).trans hx)
    ((value?_model_unpack32 y).trans hy) hb

/-- The inexact flag of division holds exactly when the value returned by
`divWith` differs from the exact quotient (IEEE 754-2019 §7.6). -/
theorem divFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hb : b ≠ 0) :
    (x.divFlags mode tininess y).inexact = true ↔ (divWith mode x y).toRat? ≠ some (a / b) := by
  obtain ⟨nx, hdx⟩ := (F32.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F32.toRat?_eq_some_iff y b).mp hy
  rw [divFlags, hdx, hdy, div_finite _ _ _ _ _ _ hb, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, divWith_rounded? mode hx hy hb, Option.some.injEq]

theorem sqrtWith_rounded? (mode : RoundingMode) {x : F32} {a : ℚ}
    (hx : x.toRat? = some a) (ha : 0 ≤ a) :
    (sqrtWith mode x).rounded?.map Rounded.cast =
      some (deliver .binary32 mode (Real.sqrt (a : ℝ))) :=
  roundedOf?_unpack_sqrtRounded .binary32 mode ((value?_model_unpack32 x).trans hx) ha

/-- The inexact flag of square root holds exactly when the value returned by
`sqrtWith` is not the exact real square root (IEEE 754-2019 §7.6). -/
theorem sqrtFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x : F32} {a : ℚ}
    (hx : x.toRat? = some a) (ha : 0 ≤ a) :
    (x.sqrtFlags mode tininess).inexact = true ↔
      ¬ ∃ v : ℚ, (sqrtWith mode x).toRat? = some v ∧ (v : ℝ) = Real.sqrt (a : ℝ) := by
  obtain ⟨nx, hdx⟩ := (F32.toRat?_eq_some_iff x a).mp hx
  rw [sqrtFlags, hdx, sqrt_finite _ _ _ _ ha, roundingFlags_inexact]
  refine (inexact_iff_of_map_cast _ _ (sqrtWith_rounded? mode hx ha)).trans ?_
  simp only [toRat?_eq_iff_rounded?]

end F32

namespace F64

theorem divWith_rounded? (mode : RoundingMode) {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hb : b ≠ 0) :
    (divWith mode x y).rounded? = some (deliver .binary64 mode (a / b)) :=
  roundedOf?_unpack_divRounded .binary64 mode ((value?_model_unpack64 x).trans hx)
    ((value?_model_unpack64 y).trans hy) hb

/-- The inexact flag of division holds exactly when the value returned by
`divWith` differs from the exact quotient (IEEE 754-2019 §7.6). -/
theorem divFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hb : b ≠ 0) :
    (x.divFlags mode tininess y).inexact = true ↔ (divWith mode x y).toRat? ≠ some (a / b) := by
  obtain ⟨nx, hdx⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  obtain ⟨ny, hdy⟩ := (F64.toRat?_eq_some_iff y b).mp hy
  rw [divFlags, hdx, hdy, div_finite _ _ _ _ _ _ hb, roundingFlags_inexact, ne_eq, ne_eq,
    toRat?_eq_iff_rounded?, divWith_rounded? mode hx hy hb, Option.some.injEq]

theorem sqrtWith_rounded? (mode : RoundingMode) {x : F64} {a : ℚ}
    (hx : x.toRat? = some a) (ha : 0 ≤ a) :
    (sqrtWith mode x).rounded?.map Rounded.cast =
      some (deliver .binary64 mode (Real.sqrt (a : ℝ))) :=
  roundedOf?_unpack_sqrtRounded .binary64 mode ((value?_model_unpack64 x).trans hx) ha

/-- The inexact flag of square root holds exactly when the value returned by
`sqrtWith` is not the exact real square root (IEEE 754-2019 §7.6). -/
theorem sqrtFlags_inexact_iff (mode : RoundingMode) (tininess : Tininess) {x : F64} {a : ℚ}
    (hx : x.toRat? = some a) (ha : 0 ≤ a) :
    (x.sqrtFlags mode tininess).inexact = true ↔
      ¬ ∃ v : ℚ, (sqrtWith mode x).toRat? = some v ∧ (v : ℝ) = Real.sqrt (a : ℝ) := by
  obtain ⟨nx, hdx⟩ := (F64.toRat?_eq_some_iff x a).mp hx
  rw [sqrtFlags, hdx, sqrt_finite _ _ _ _ ha, roundingFlags_inexact]
  refine (inexact_iff_of_map_cast _ _ (sqrtWith_rounded? mode hx ha)).trans ?_
  simp only [toRat?_eq_iff_rounded?]

end F64

end Silmaril.Numeric.Ieee754
