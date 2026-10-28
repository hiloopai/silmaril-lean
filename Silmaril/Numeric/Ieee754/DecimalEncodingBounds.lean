module

public import Silmaril.Numeric.Ieee754.DecimalBounds
public import Silmaril.Numeric.Ieee754.EncodingCorrectness
public import Silmaril.Numeric.Ieee754.BinaryMagnitude

/-! # Binary64 encoding bounds for complete decimal search

Every positive finite binary64 encoding has sufficient spacing to both
neighbors for the exact 1–17-digit search. The proof uses arithmetic field
transitions, including all subnormal and binade cases, rather than enumerating
the interchange space. At maximum finite the formatter uses its existing
extrapolated upper endpoint.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

/-- The actual core-decoded rational agrees with the unsigned magnitude
formula throughout the sign-clear finite range, including positive zero. -/
theorem rational_eq_binaryMagnitude (bits : UInt64)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    rational bits = BinaryMagnitude.value 52 1023 bits.toNat := by
  have signBound : bits.toNat < 2 ^ 63 := by norm_num at finite ⊢; omega
  have exponentBound : bits.toNat / 2 ^ 52 < 2047 := by norm_num at finite ⊢; omega
  have signZero : bits.toNat / 2 ^ 63 = 0 := Nat.div_eq_of_lt signBound
  have exponentMod : bits.toNat / 2 ^ 52 % 2 ^ 11 = bits.toNat / 2 ^ 52 :=
    Nat.mod_eq_of_lt (by norm_num; omega)
  have fields : decode64 bits.toNat = ⟨false, bits.toNat / 2 ^ 52, bits.toNat % 2 ^ 52⟩ := by
    norm_num at signZero exponentMod
    simp only [decode64, decode, field, binary64ExponentBits, binary64SignificandBits]
    norm_num only
    simp only [Nat.div_eq_of_lt signZero, Nat.mod_eq_of_lt exponentMod, Nat.div_one, Nat.zero_mod]
    rfl
  have notExceptional : bits.toNat / 2 ^ 52 ≠ maxExponentField 11 := by
    norm_num [maxExponentField]
    omega
  norm_num [maxExponentField] at notExceptional
  rw [BinaryMagnitude.value_field_formula]
  simp only [rational, Conformance.value?_model_unpack64, F64.toRat?, F64.ofBits, value64?, fields]
  simp [finiteValue, binary64ExponentBits, binary64SignificandBits, binary64Bias,
    maxExponentField, notExceptional, signed, BinaryMagnitude.radix]
  split_ifs <;> rfl

theorem rational_pos_of_positive_finite (bits : UInt64)
    (positive : 0 < bits.toNat) (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    0 < rational bits := by
  rw [rational_eq_binaryMagnitude bits finite]
  exact BinaryMagnitude.value_pos 52 1023 bits.toNat positive

/-- The preceding UInt64 encoding is an ordinary natural predecessor on the
nonzero finite positive domain. -/
theorem predecessor_toNat (bits : UInt64) (positive : 0 < bits.toNat) :
    (bits - 1).toNat = bits.toNat - 1 := by
  apply UInt64.toNat_sub_of_le
  change 1 ≤ bits.toNat
  omega

/-- The following UInt64 encoding cannot wrap in the positive finite range. -/
theorem successor_toNat (bits : UInt64) (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    (bits + 1).toNat = bits.toNat + 1 := by
  rw [UInt64.toNat_add]
  apply Nat.mod_eq_of_lt
  change bits.toNat + 1 < 2 ^ 64
  norm_num at finite ⊢
  omega

/-- Relative lower spacing, including the asymmetric normal binade boundary. -/
theorem positive_finite_lower_gap (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    rational bits / 2 ^ 53 ≤ rational bits - rational (bits - 1) := by
  have predecessor := predecessor_toNat bits positive
  have previousFinite : (bits - 1).toNat ≤ 0x7fefffffffffffff := by rw [predecessor]; omega
  rw [rational_eq_binaryMagnitude bits finite, rational_eq_binaryMagnitude (bits - 1) previousFinite,
    predecessor]
  have bound := (BinaryMagnitude.relative_gap 52 1023 (bits.toNat - 1)).2
  have successor : bits.toNat - 1 + 1 = bits.toNat := by omega
  rw [successor] at bound
  norm_num only [BinaryMagnitude.radix] at bound ⊢
  exact bound

/-- Relative upper spacing, for every encoding below maximum finite. -/
theorem positive_finite_upper_gap (bits : UInt64) (finite : bits.toNat ≤ 0x7fefffffffffffff)
    (notMaximum : bits ≠ 0x7fefffffffffffff) :
    rational bits / 2 ^ 53 ≤ rational (bits + 1) - rational bits := by
  have different : bits.toNat ≠ 0x7fefffffffffffff := by
    intro equal
    apply notMaximum
    exact UInt64.toNat_inj.mp equal
  have successor := successor_toNat bits finite
  have nextFinite : (bits + 1).toNat ≤ 0x7fefffffffffffff := by rw [successor]; omega
  rw [rational_eq_binaryMagnitude bits finite, rational_eq_binaryMagnitude (bits + 1) nextFinite,
    successor]
  have bound := (BinaryMagnitude.relative_gap 52 1023 bits.toNat).1
  norm_num only [BinaryMagnitude.radix] at bound ⊢
  exact bound

/-- The actual formatter always finds a candidate among precisions 1–17
for every nonzero sign-clear finite binary64 encoding. -/
theorem shortest_search_success_of_positive_finite (bits : UInt64)
    (positive : 0 < bits.toNat) (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    ∃ number, firstCandidate (roundingInterval bits) (rational bits)
      (List.range' 1 17) = some number :=
  shortest_search_success_of_gaps bits (rational_pos_of_positive_finite bits positive finite)
    (positive_finite_lower_gap bits positive finite) (positive_finite_upper_gap bits finite)

/-- The selected decimal lies in the actual binary64 neighbor interval,
without conditional gap assumptions or use of the exact-decimal fallback. -/
theorem shortest_accepts_of_positive_finite (bits : UInt64)
    (positive : 0 < bits.toNat) (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    (roundingInterval bits).accepts (shortest bits).value = true :=
  shortest_accepts_of_gaps bits (rational_pos_of_positive_finite bits positive finite)
    (positive_finite_lower_gap bits positive finite) (positive_finite_upper_gap bits finite)

/-- Convenient statement directly in the unsigned binary64 ordering. -/
theorem shortest_search_success (bits : UInt64) (positive : 0 < bits)
    (finite : bits ≤ 0x7fefffffffffffff) :
    ∃ number, firstCandidate (roundingInterval bits) (rational bits)
      (List.range' 1 17) = some number :=
  shortest_search_success_of_positive_finite bits positive finite

end Silmaril.Numeric.Ieee754.Decimal
