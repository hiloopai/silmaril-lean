module

public import Silmaril.Numeric.Ieee754.Flags.Rounding
public import Silmaril.Numeric.Ieee754.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Bitwise

/-!
# Operands as seen by exception classification

A `Datum` records what IEEE 754-2019 exception rules inspect in an operand:
whether it is a NaN and whether that NaN is signaling (§6.2), the sign of an
infinity, and the exact rational value and sign bit of a finite number. NaN
payloads are dropped, since no exception depends on them.

`Datum.decode` reads a binary interchange encoding of any `Format` (§3.4). A NaN
is signaling when the most significant trailing-significand bit is clear; this
is the encoding recommended by §6.2.1 and the one used by the x86-64, AArch64 and
RISC-V floating-point architectures. The core model's `UnpackedFloat` erases this
distinction, which is why classification starts from the raw encoding.

For binary32 and binary64, `F32.datum` and `F64.datum` agree with the existing
wrappers: the finite value is `toRat?` and the signaling bit is
`isSignalingNaN`. Every decoded finite value is a representable value of its
format (`decode_finite_representable`).
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model

/-- An operand as seen by exception classification. `finite negative value`
keeps the sign bit, which distinguishes the zeros, and the exact value. -/
inductive Datum where
  | nan (signaling : Bool)
  | infinity (negative : Bool)
  | finite (negative : Bool) (value : ℚ)
  deriving DecidableEq, Repr

namespace Datum

/-- A signaling NaN (§6.2). -/
def isSignaling : Datum → Bool
  | .nan signaling => signaling
  | _ => false

/-- Any NaN. -/
def isNaN : Datum → Bool
  | .nan _ => true
  | _ => false

/-- A quiet NaN. -/
def isQuietNaN : Datum → Bool
  | .nan signaling => !signaling
  | _ => false

/-- Either infinity. -/
def isInfinite : Datum → Bool
  | .infinity _ => true
  | _ => false

/-- Either zero. -/
def isZero : Datum → Bool
  | .finite _ value => value == 0
  | _ => false

/-- The sign of a non-NaN operand: the sign bit of a zero or infinity, and the
sign of the value otherwise. -/
def negative : Datum → Bool
  | .nan _ => false
  | .infinity negative => negative
  | .finite negative value => if value = 0 then negative else decide (value < 0)

/-- Negation (§5.5.1), used to express subtraction as addition. -/
def neg : Datum → Datum
  | .nan signaling => .nan signaling
  | .infinity negative => .infinity (!negative)
  | .finite negative value => .finite (!negative) (-value)

@[simp] theorem isSignaling_neg (x : Datum) : x.neg.isSignaling = x.isSignaling := by
  cases x <;> rfl

@[simp] theorem isNaN_neg (x : Datum) : x.neg.isNaN = x.isNaN := by
  cases x <;> rfl

theorem isNaN_of_isSignaling {x : Datum} (h : x.isSignaling = true) : x.isNaN = true := by
  cases x <;> simp_all [isSignaling, isNaN]

/-- Classify decoded interchange fields with `w` exponent bits, `t`
trailing-significand bits and the given bias (§3.4, §6.2.1). -/
def ofDecoded (w t : Nat) (bias : Int) (d : Decoded) : Datum :=
  match finiteValue w t bias d with
  | some value => .finite d.sign value
  | none =>
    if d.trailingSignificand = 0 then .infinity d.sign
    else .nan (decide (d.trailingSignificand < 2 ^ (t - 1)))

/-- Classify a raw interchange encoding of a format. -/
def decode (f : Format) (bits : Nat) : Datum :=
  ofDecoded f.exponentBits f.mantissaBitsWithoutImplicit f.exponentBias
    (Ieee754.decode f.exponentBits f.mantissaBitsWithoutImplicit bits)

end Datum

/-! ## Decoded finite values are representable -/

theorem representable_neg {f : Format} {x : ℚ} (h : Representable f x) : Representable f (-x) := by
  obtain ⟨n, q, rfl, hn, hq, hmax⟩ := h
  exact ⟨-n, q, by push_cast; ring, by rwa [abs_neg], hq, by rwa [abs_neg]⟩

/-- A significand below `2 ^ p` on a grid between the subnormal spacing and the
spacing of the largest binade gives a finite value. -/
theorem representable_of_significand (f : Format) {n q : ℤ} (hn : |n| < 2 ^ f.mantissaBits)
    (hq : minQuantum f ≤ q) (hq' : q ≤ maxQuantum f) : Representable f ((n : ℚ) * 2 ^ q) := by
  refine ⟨n, q, rfl, hn, hq, ?_⟩
  have hsig : |n| ≤ maxSignificand f := by unfold maxSignificand; omega
  rw [abs_mul, abs_of_pos (two_zpow_pos (K := ℚ) q)]
  unfold maxFinite
  apply mul_le_mul _ (zpow_le_zpow_right₀ (by norm_num) hq') (two_zpow_pos q).le
    (by exact_mod_cast (maxSignificand_pos f).le)
  rw [← Int.cast_abs]
  exact_mod_cast hsig

theorem representable_signed {f : Format} (negative : Bool) {x : ℚ} (h : Representable f x) :
    Representable f (signed negative x) := by
  cases negative
  · exact h
  · exact representable_neg h

/-- Every finite decoded value of a format is representable in that format. -/
theorem decode_finite_representable (f : Format) (bits : Nat) {negative : Bool} {value : ℚ}
    (h : Datum.decode f bits = .finite negative value) : Representable f value := by
  unfold Datum.decode Datum.ofDecoded at h
  generalize hd : Ieee754.decode f.exponentBits f.mantissaBitsWithoutImplicit bits = d at h
  have hT : d.trailingSignificand < 2 ^ f.mantissaBitsWithoutImplicit := by
    rw [← hd]
    exact Nat.mod_lt _ (by positivity)
  have hE : d.exponent < 2 ^ f.exponentBits := by
    rw [← hd]
    exact Nat.mod_lt _ (by positivity)
  have hw := f.he
  have hbias : emax f = (2 : ℤ) ^ (f.exponentBits - 1) - 1 := emax_eq f
  have hpow : (2 : ℤ) ^ f.exponentBits = 2 * 2 ^ (f.exponentBits - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hmb : f.mantissaBits = f.mantissaBitsWithoutImplicit + 1 := by
    change 1 + f.mantissaBitsWithoutImplicit = _
    omega
  have hmin : minQuantum f = 1 - emax f - f.mantissaBitsWithoutImplicit := by
    unfold minQuantum emin precision
    rw [hmb]
    push_cast
    ring
  have hmaxq : maxQuantum f = emax f - f.mantissaBitsWithoutImplicit := by
    unfold maxQuantum precision
    rw [hmb]
    push_cast
    ring
  have hTint : ((d.trailingSignificand : ℕ) : ℤ) < 2 ^ f.mantissaBitsWithoutImplicit := by
    exact_mod_cast hT
  have h2t : ((2 ^ f.mantissaBitsWithoutImplicit : ℕ) : ℚ) =
      (2 : ℚ) ^ (f.mantissaBitsWithoutImplicit : ℤ) := by
    push_cast
    rfl
  have hbiasEq : ((f.exponentBias : ℕ) : ℤ) = emax f := rfl
  cases hfv : finiteValue f.exponentBits f.mantissaBitsWithoutImplicit f.exponentBias d with
  | none =>
    rw [hfv] at h
    dsimp only at h
    split at h <;> cases h
  | some v =>
    rw [hfv] at h
    cases h
    unfold finiteValue at hfv
    simp only [beq_iff_eq] at hfv
    split at hfv
    · cases hfv
    · next hEm =>
      have hEmax : (d.exponent : ℤ) ≤ 2 ^ f.exponentBits - 2 := by
        have : d.exponent < 2 ^ f.exponentBits - 1 := by
          unfold maxExponentField at hEm
          omega
        have hc : ((2 ^ f.exponentBits - 1 : ℕ) : ℤ) = 2 ^ f.exponentBits - 1 := by
          rw [Nat.cast_sub Nat.one_le_two_pow]
          push_cast
          ring
        omega
      split at hfv
      · -- Zero or subnormal: `T · 2 ^ (emin - t)`.
        simp only [Option.some.injEq] at hfv
        subst hfv
        apply representable_signed
        have hval : (d.trailingSignificand : ℚ) / ((2 ^ f.mantissaBitsWithoutImplicit : ℕ) : ℚ) *
            (2 : ℚ) ^ (1 - ((f.exponentBias : ℕ) : ℤ)) =
            ((d.trailingSignificand : ℤ) : ℚ) * 2 ^ minQuantum f := by
          rw [h2t, hbiasEq, hmin, show 1 - emax f - (f.mantissaBitsWithoutImplicit : ℤ) =
            (1 - emax f) + (-(f.mantissaBitsWithoutImplicit : ℤ)) by ring,
            zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_neg]
          push_cast
          field_simp
        rw [hval]
        apply representable_of_significand f _ le_rfl
        · rw [hmin, hmaxq]
          have := one_le_emax f
          omega
        · rw [abs_of_nonneg (by positivity), hmb, pow_succ]
          have : (0 : ℤ) < 2 ^ f.mantissaBitsWithoutImplicit := by positivity
          linarith
      · -- Normal: `(2 ^ t + T) · 2 ^ (E - bias - t)`.
        next hE0 =>
        simp only [Option.some.injEq] at hfv
        subst hfv
        apply representable_signed
        have hval : (1 + (d.trailingSignificand : ℚ) /
            ((2 ^ f.mantissaBitsWithoutImplicit : ℕ) : ℚ)) *
            (2 : ℚ) ^ ((d.exponent : ℤ) - ((f.exponentBias : ℕ) : ℤ)) =
            (((2 ^ f.mantissaBitsWithoutImplicit + d.trailingSignificand : ℕ) : ℤ) : ℚ) *
              2 ^ ((d.exponent : ℤ) - emax f - f.mantissaBitsWithoutImplicit) := by
          rw [h2t, hbiasEq, show (d.exponent : ℤ) - emax f - (f.mantissaBitsWithoutImplicit : ℤ) =
            ((d.exponent : ℤ) - emax f) + (-(f.mantissaBitsWithoutImplicit : ℤ)) by ring,
            zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_neg]
          push_cast
          rw [zpow_natCast]
          field_simp
        rw [hval]
        apply representable_of_significand f
        · rw [abs_of_nonneg (by positivity), hmb, pow_succ]
          push_cast
          linarith
        · rw [hmin]
          have : (1 : ℤ) ≤ d.exponent := by omega
          omega
        · rw [hmaxq]
          omega

end Silmaril.Numeric.Ieee754.FlagSpec

/-! ## Binary32 and binary64 operands -/

namespace Silmaril.Numeric.Ieee754

open Float.Model FlagSpec

/-- The classification of a raw binary32 encoding. -/
def F32.datum (x : F32) : Datum :=
  Datum.decode Format.binary32 x.bits.toNat

/-- The classification of a raw binary64 encoding. -/
def F64.datum (x : F64) : Datum :=
  Datum.decode Format.binary64 x.bits.toNat

theorem F32.datum_eq (x : F32) :
    x.datum = Datum.ofDecoded binary32ExponentBits binary32SignificandBits binary32Bias
      (decode32 x.bits.toNat) := rfl

theorem F64.datum_eq (x : F64) :
    x.datum = Datum.ofDecoded binary64ExponentBits binary64SignificandBits binary64Bias
      (decode64 x.bits.toNat) := rfl

/-- A finite binary32 operand carries exactly its rational value `toRat?`. -/
theorem F32.toRat?_eq_some_iff (x : F32) (value : ℚ) :
    x.toRat? = some value ↔ ∃ negative, x.datum = .finite negative value := by
  rw [F32.datum_eq, F32.toRat?, value32?]
  unfold Datum.ofDecoded
  split
  · next v hv =>
    rw [hv]
    simp
  · next hv =>
    rw [hv]
    split <;> simp

/-- A finite binary64 operand carries exactly its rational value `toRat?`. -/
theorem F64.toRat?_eq_some_iff (x : F64) (value : ℚ) :
    x.toRat? = some value ↔ ∃ negative, x.datum = .finite negative value := by
  rw [F64.datum_eq, F64.toRat?, value64?]
  unfold Datum.ofDecoded
  split
  · next v hv =>
    rw [hv]
    simp
  · next hv =>
    rw [hv]
    split <;> simp

private theorem uint32_quietBit (u : UInt32) :
    (u &&& 0x00400000 == 0) = decide (u.toNat / 2 ^ 22 % 2 ≠ 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt32.toNat_inj, UInt32.toNat_and,
    show (0x00400000 : UInt32).toNat = 2 ^ 22 from rfl, show (0 : UInt32).toNat = 0 from rfl,
    Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : u.toNat / 2 ^ 22 % 2 = 1 <;> simp_all

private theorem uint64_quietBit (u : UInt64) :
    (u &&& 0x0008000000000000 == 0) = decide (u.toNat / 2 ^ 51 % 2 ≠ 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, UInt64.toNat_and,
    show (0x0008000000000000 : UInt64).toNat = 2 ^ 51 from rfl, show (0 : UInt64).toNat = 0 from rfl,
    Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : u.toNat / 2 ^ 51 % 2 = 1 <;> simp_all

private theorem signaling32 (b : ℕ) :
    (Datum.ofDecoded binary32ExponentBits binary32SignificandBits binary32Bias
      (decode32 b)).isSignaling =
    (decide (classify32 b = .nan) && decide (b / 2 ^ 22 % 2 ≠ 1)) := by
  simp only [Datum.ofDecoded, finiteValue, classify32, classify, decode32, Ieee754.decode, field,
    maxExponentField, binary32ExponentBits, binary32SignificandBits, Nat.reducePow, Nat.reduceSub,
    beq_iff_eq]
  split_ifs <;> simp_all [Datum.isSignaling]
  omega

private theorem signaling64 (b : ℕ) :
    (Datum.ofDecoded binary64ExponentBits binary64SignificandBits binary64Bias
      (decode64 b)).isSignaling =
    (decide (classify64 b = .nan) && decide (b / 2 ^ 51 % 2 ≠ 1)) := by
  simp only [Datum.ofDecoded, finiteValue, classify64, classify, decode64, Ieee754.decode, field,
    maxExponentField, binary64ExponentBits, binary64SignificandBits, Nat.reducePow, Nat.reduceSub,
    beq_iff_eq]
  split_ifs <;> simp_all [Datum.isSignaling]
  omega

/-- The signaling test agrees with the existing binary32 bit test (§6.2.1). -/
theorem F32.datum_isSignaling (x : F32) : x.datum.isSignaling = x.isSignalingNaN := by
  rw [F32.isSignalingNaN, uint32_quietBit, F32.datum_eq, signaling32]
  rfl

/-- The signaling test agrees with the existing binary64 bit test (§6.2.1). -/
theorem F64.datum_isSignaling (x : F64) : x.datum.isSignaling = x.isSignalingNaN := by
  rw [F64.isSignalingNaN, uint64_quietBit, F64.datum_eq, signaling64]
  rfl

theorem F32.datum_finite_representable (x : F32) {negative : Bool} {value : ℚ}
    (h : x.datum = .finite negative value) : Representable Format.binary32 value :=
  decode_finite_representable _ _ h

theorem F64.datum_finite_representable (x : F64) {negative : Bool} {value : ℚ}
    (h : x.datum = .finite negative value) : Representable Format.binary64 value :=
  decode_finite_representable _ _ h

end Silmaril.Numeric.Ieee754
