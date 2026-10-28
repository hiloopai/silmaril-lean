module

public import Silmaril.Numeric.Ieee754.Rounding.Packing

/-! # Canonical form of the executable rounder's results -/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Rounding

open Float.Model Float.Model.UnpackedFloat

theorem shift_target_small (format : Format) (m : Nat) (e : Int)
    (hm : m < 2 ^ format.mantissaBits) (he : format.minExponent ≤ e) :
    shiftToTargetExponent format m e .exact = (⟨m, false, false⟩, e) := by
  have hlog : m.log2 + 1 ≤ format.mantissaBits := by
    by_cases hz : m = 0
    · subst m
      simp [Format.mantissaBits]
    · exact Nat.succ_le_of_lt ((Nat.log2_lt hz).mpr hm)
  have ht : format.targetExponent (totalExponent m e) ≤ e := by
    simp only [Format.targetExponent, totalExponent]
    apply max_le _ he
    omega
  have hn : (format.targetExponent (totalExponent m e) - e).toNat = 0 := by omega
  simp only [shiftToTargetExponent, shiftToExponent, hn, Int.natCast_zero, add_zero]
  rfl

theorem shift_target_carry (format : Format) (e : Int) (he : format.minExponent ≤ e) :
    shiftToTargetExponent format (2 ^ format.mantissaBits) e .exact =
      (⟨2 ^ format.mantissaBitsWithoutImplicit, false, false⟩, e + 1) := by
  have ht : format.targetExponent (totalExponent (2 ^ format.mantissaBits) e) = e + 1 := by
    simp only [Format.targetExponent, totalExponent, Nat.log2_two_pow]
    rw [max_eq_left (by omega)]
    omega
  have hn : (e + 1 - e).toNat = 1 := by omega
  simp only [shiftToTargetExponent, shiftToExponent, ht, hn]
  change ((⟨2 ^ format.mantissaBits / 2, 2 ^ format.mantissaBits % 2 != 0, false⟩ : ExtendedMantissa), e + 1) = _
  simp [Format.mantissaBits, pow_add]

theorem normalize_canonical (format : Format) (m : Nat) (e : Int)
    (hm : m ≤ 2 ^ format.mantissaBits) (he : format.minExponent ≤ e)
    (hs : m < 2 ^ format.mantissaBitsWithoutImplicit → e = format.minExponent) :
    Canonical format (shiftToTargetExponent format m e .exact).1.mantissa
      (shiftToTargetExponent format m e .exact).2 := by
  by_cases hsmall : m < 2 ^ format.mantissaBits
  · rw [shift_target_small format m e hsmall he]
    exact ⟨hsmall, he, hs⟩
  · have hm' : m = 2 ^ format.mantissaBits := by omega
    subst m
    rw [shift_target_carry format e he]
    constructor
    · simp only [Format.mantissaBits, Nat.add_comm 1, pow_succ]
      have hp : 0 < 2 ^ format.mantissaBitsWithoutImplicit := by positivity
      omega
    · omega
    · intro h
      exact (Nat.lt_irrefl _ h).elim

theorem roundMantissa_ge (mode : RoundingMode) (sign : Sign) (m : Nat) (a : Accuracy) :
    m ≤ roundMantissa mode sign m a :=
  (Conformance.roundMantissa_bracket mode sign m a).elim (fun h => by omega) (fun h => by omega)

/-- A sufficiently low source exponent lets the first shift normalize the significand. -/
theorem firstShift_canonical (format : Format) (m : Nat) (e : Int) (a : Accuracy)
    (hm : 0 < m) (he : e ≤ format.targetExponent (totalExponent m e)) :
    Canonical format (shiftToTargetExponent format m e a).1.mantissa
      (shiftToTargetExponent format m e a).2 := by
  refine ⟨shifted_mantissa_lt format m e a, shifted_exponent_min format m e a, ?_⟩
  intro hsmall
  let target := format.targetExponent (totalExponent m e)
  let n := (target - e).toNat
  have hn : (n : Int) = target - e := by dsimp [n]; omega
  have hexp : (shiftToTargetExponent format m e a).2 = target := by
    change e + (n : Int) = target
    omega
  rw [hexp]
  by_contra hne
  have hmin : format.minExponent < target :=
    lt_of_le_of_ne (le_max_right _ _) (Ne.symm hne)
  have ht : target = totalExponent m e - format.mantissaBits := by
    dsimp [target, Format.targetExponent] at hmin ⊢
    exact max_eq_left (by omega)
  have heq : n + format.mantissaBitsWithoutImplicit = m.log2 := by
    simp only [totalExponent, Format.mantissaBits, Nat.cast_add, Nat.cast_one] at ht
    omega
  have hlow : 2 ^ format.mantissaBitsWithoutImplicit ≤ m / 2 ^ n := by
    rw [Nat.le_div_iff_mul_le (by positivity), ← pow_add, Nat.add_comm, heq]
    exact Nat.log2_self_le (Nat.ne_of_gt hm)
  change (Nat.repeat ExtendedMantissa.shiftRightOne n
    (ExtendedMantissa.ofMantissaAndAccuracy m a)).mantissa < _ at hsmall
  rw [shiftRight_mantissa] at hsmall
  have hm' : (ExtendedMantissa.ofMantissaAndAccuracy m a).mantissa = m := by
    cases a with
    | exact => rfl
    | inexact order => cases order <;> rfl
  rw [hm'] at hsmall
  omega

def CanonicalValue (format : Format) : UnpackedFloat → Prop
  | .zero _ => True
  | .finite _ m e _ => Canonical format m e
  | _ => False

theorem roundWithAccuracy_canonical (format : Format) (mode : RoundingMode)
    (sign : Sign) (m : Nat) (e : Int) (a : Accuracy)
    (hm : 0 < m) (he : e ≤ format.targetExponent (totalExponent m e)) :
    CanonicalValue format (roundWithAccuracy format mode sign m e a) := by
  let first := shiftToTargetExponent format m e a
  let rounded := roundMantissa mode sign first.1.mantissa first.1.accuracy
  have hc := firstShift_canonical format m e a hm he
  have hbound : rounded ≤ 2 ^ format.mantissaBits :=
    (roundMantissa_le_succ mode sign first.1.mantissa first.1.accuracy).trans hc.mantissa_lt
  have hlower : first.1.mantissa ≤ rounded := roundMantissa_ge mode sign _ _
  have hfinal := normalize_canonical format rounded first.2 hbound hc.exponent_min
    (fun h => hc.subnormal_exponent (Nat.lt_of_le_of_lt hlower h))
  unfold roundWithAccuracy
  dsimp only
  split
  · trivial
  · exact hfinal

theorem roundUnpacked_canonical (format : Format) (mode : RoundingMode)
    (sign : Sign) (m : Nat) (e : Int) (hm : 0 < m) :
    CanonicalValue format (roundUnpacked format mode (.finite sign m e hm)) := by
  apply roundWithAccuracy_canonical
  · simp only [Nat.shiftLeft_eq]
    exact Nat.mul_pos hm (by positivity)
  · have ht := decreaseExponent_total m e (format.targetExponent (totalExponent m e)) (Nat.ne_of_gt hm)
    simp only [decreaseExponent] at ht
    rw [ht]
    omega

end Silmaril.Numeric.Ieee754.Rounding
