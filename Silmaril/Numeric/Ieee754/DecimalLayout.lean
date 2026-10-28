module

public import Silmaril.Numeric.Ieee754.DecimalSelection
public import Silmaril.Numeric.DecimalTextProperties
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exact meaning of rendered decimal layouts

The actual formatter's strings are parsed by the independent executable
DecimalText parser. Padding zeros, splitting digits around the decimal point,
and scientific exponents preserve the selected rational value.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

open DecimalText

@[simp] theorem zeros_toList (count : Nat) : (zeros count).toList = List.replicate count '0' := by
  simp only [zeros, String.toList_ofList]

/-- Exponent padding and its explicit sign decode to the original integer. -/
theorem parse_exponentString (exponent : Int) :
    parseExponent (exponentString exponent).toList = some exponent := by
  let digits := (toString exponent.natAbs).toList
  let padding := List.replicate (2 - (toString exponent.natAbs).length) '0'
  have valid : Digits (padding ++ digits) := (digits_zeros _).append (digits_repr _)
  have nonempty : padding ++ digits ≠ [] := by
    have lengthPositive : 0 < digits.length := by
      simpa only [digits, String.length_toList, Nat.toString_eq_repr] using (Nat.length_repr_pos (n := exponent.natAbs))
    intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_append, List.length_nil] at lengths
    omega
  have parsed := parseNat_digits (padding ++ digits) valid nonempty
  have value : digitsValue (padding ++ digits) = exponent.natAbs := by
    rw [digitsValue_append]
    simp only [padding, digits, digitsValue_zeros, Nat.mul_zero, Nat.zero_add, digitsValue_repr]
  rw [value] at parsed
  unfold exponentString
  rw [String.toList_append, String.toList_append, zeros_toList]
  by_cases negative : exponent < 0
  · rw [ite_eq_left negative]
    change (parseNat (padding ++ digits)).map (fun n => -(n : Int)) = some exponent
    rw [parsed]
    exact congrArg some (Int.eq_neg_natAbs_of_nonpos negative.le).symm
  · rw [ite_eq_right negative]
    change (parseNat (padding ++ digits)).map Int.ofNat = some exponent
    rw [parsed]
    exact congrArg some (Int.ofNat_natAbs_of_nonneg (le_of_not_gt negative))

/-- Inserting a decimal point after any positive number of digits leaves an
exactly predictable power of ten, including a point beyond the final digit. -/
theorem scan_split_digits (digits : List Char) (valid : Digits digits) (count : Nat)
    (positive : 0 < count) (nonempty : digits ≠ []) :
    scan (digits.take count ++ '.' :: digits.drop count) 0 0 false false =
      some (finish (digitsValue digits) (digits.length - count) 0) := by
  have beforeNonempty : digits.take count ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_take, List.length_nil] at lengths
    have digitsPositive : 0 < digits.length := List.length_pos_iff.mpr nonempty
    omega
  simpa only [List.take_append_drop, List.length_drop] using
    scan_fixed (digits.take count) (digits.drop count) (valid.take _) (valid.drop _) beforeNonempty

/-- The actual string renderer preserves every decimal Number's
rational value, including all four fixed/scientific layout branches. -/
theorem scan_layout (input : Number) :
    scan (layout input).toList 0 0 false false = some input.value := by
  let number := input.normalize
  let digits := (toString number.coefficient).toList
  let point : Int := (digits.length : Int) + number.exponent
  have valid : Digits digits := digits_repr _
  have digitsPositive : 0 < digits.length := by
    simpa only [digits, String.length_toList, Nat.toString_eq_repr] using (Nat.length_repr_pos (n := number.coefficient))
  have nonempty : digits ≠ [] := List.ne_nil_of_length_pos digitsPositive
  have digitsValue : DecimalText.digitsValue digits = number.coefficient := digitsValue_repr _
  have numberValue : number.value = input.value := input.normalize_value
  have zeroValid : Digits ['0'] := digits_zeros 1
  change scan ((if point ≤ -4 ∨ 16 < point then
      String.ofList (digits.take 1) ++
        (if digits.length > 1 then "." ++ String.ofList (digits.drop 1) else "") ++
        "e" ++ exponentString (point - 1)
    else if point ≤ 0 then "0." ++ zeros (-point).toNat ++ String.ofList digits
    else if point.toNat < digits.length then
      String.ofList (digits.take point.toNat) ++ "." ++ String.ofList (digits.drop point.toNat)
    else String.ofList digits ++ zeros (point.toNat - digits.length) ++ ".0").toList)
    0 0 false false = some input.value
  split
  next scientific =>
    have beforeNonempty : digits.take 1 ≠ [] := by
      intro empty
      have lengths := congrArg List.length empty
      simp only [List.length_take, List.length_nil] at lengths
      omega
    split
    next fractional =>
      simp only [String.toList_append, String.toList_ofList, List.append_assoc]
      change scan (digits.take 1 ++ '.' :: (digits.drop 1 ++ 'e' :: (exponentString (point - 1)).toList))
        0 0 false false = _
      rw [scan_scientific _ _ _ (valid.take _) (valid.drop _) beforeNonempty (parse_exponentString _),
        List.take_append_drop, digitsValue]
      congr 1
      unfold finish
      rw [List.length_drop]
      have exponentEqual : point - 1 - ((digits.length - 1 : Nat) : Int) = number.exponent := by
        dsimp only [point]
        omega
      rw [exponentEqual]
      exact numberValue
    next integral =>
      have lengthOne : digits.length = 1 := by omega
      have takeAll : digits.take 1 = digits := List.take_of_length_le (by omega)
      simp only [String.toList_append, String.toList_ofList, takeAll]
      simp only [show "".toList = [] from rfl, List.append_nil, List.append_assoc]
      change scan (digits ++ 'e' :: (exponentString (point - 1)).toList) 0 0 false false = _
      rw [scan_integer_scientific _ _ valid nonempty (parse_exponentString _), digitsValue]
      congr 1
      have exponentEqual : point - 1 = number.exponent := by dsimp only [point]; omega
      simpa only [finish, Nat.cast_zero, sub_zero, exponentEqual, Number.value, power] using numberValue
  next fixed =>
    split
    next leading =>
      simp only [String.toList_append, zeros_toList, String.toList_ofList]
      change scan (['0'] ++ '.' :: (List.replicate (-point).toNat '0' ++ digits)) 0 0 false false = _
      rw [scan_fixed _ _ zeroValid ((digits_zeros _).append valid) (by decide)]
      congr 1
      have coefficientEqual : DecimalText.digitsValue (['0'] ++ (List.replicate (-point).toNat '0' ++ digits)) =
          number.coefficient := by
        simp only [DecimalText.digitsValue, Nat.ofDigitChars_append, Nat.ofDigitChars_cons,
          Nat.ofDigitChars_nil, Char.reduceToNat, Nat.sub_self, Nat.mul_zero, Nat.zero_add,
          Nat.ofDigitChars_replicate_zero]
        exact digitsValue
      rw [coefficientEqual]
      unfold finish
      have exponentEqual : (0 : Int) - ((List.replicate (-point).toNat '0' ++ digits).length : Int) =
          number.exponent := by
        rw [List.length_append, List.length_replicate, Nat.cast_add,
          Int.toNat_of_nonneg (by omega : 0 ≤ -point)]
        dsimp only [point]
        omega
      rw [exponentEqual]
      exact numberValue
    next notLeading =>
      split
      next middle =>
        simp only [String.toList_append, String.toList_ofList, List.append_assoc]
        change scan (digits.take point.toNat ++ '.' :: digits.drop point.toNat) 0 0 false false = _
        rw [scan_split_digits digits valid point.toNat (by omega) nonempty, digitsValue]
        congr 1
        unfold finish
        have exponentEqual : (0 : Int) - ((digits.length - point.toNat : Nat) : Int) = number.exponent := by
          have pointNat : (point.toNat : Int) = point := Int.toNat_of_nonneg (by omega)
          dsimp only [point] at pointNat
          omega
        rw [exponentEqual]
        exact numberValue
      next trailing =>
        simp only [String.toList_append, zeros_toList, String.toList_ofList]
        change scan ((digits ++ List.replicate (point.toNat - digits.length) '0') ++ '.' :: ['0'])
          0 0 false false = _
        rw [scan_fixed _ _ (valid.append (digits_zeros _)) zeroValid
          (by intro empty; have lengths := congrArg List.length empty; simp only [List.length_append, List.length_nil, List.length_replicate] at lengths; omega)]
        congr 1
        rw [digitsValue_append, digitsValue_append, digitsValue]
        simp only [digitsValue_zeros, List.length_replicate, List.length_singleton,
          show DecimalText.digitsValue ['0'] = 0 from digitsValue_zeros 1]
        change ((10 ^ 1 * (10 ^ (point.toNat - digits.length) * number.coefficient + 0) + 0 : Nat) : ℚ) *
          (10 : ℚ) ^ ((0 : Int) - 1) = input.value
        have exponentEqual : ((point.toNat - digits.length : Nat) : Int) = number.exponent := by
          have pointNat : (point.toNat : Int) = point := Int.toNat_of_nonneg (by omega)
          dsimp only [point] at pointNat
          omega
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, add_zero,
          pow_one, zero_sub, zpow_neg, zpow_one]
        rw [← zpow_natCast (10 : ℚ) (point.toNat - digits.length), exponentEqual]
        calc
          _ = (number.coefficient : ℚ) * (10 : ℚ) ^ number.exponent := by ring
          _ = input.value := numberValue

/-- Full executable parsing, rather than a separate layout denotation. -/
theorem parse_layout (input : Number) :
    DecimalText.parse (layout input) = some (.finite ⟨false, input.value⟩) :=
  parse_unsigned_of_scan _ _ (scan_layout input)

theorem parse_negative_layout (input : Number) :
    DecimalText.parse ("-" ++ layout input) = some (.finite ⟨true, input.value⟩) :=
  parse_negative_of_scan _ _ (scan_layout input)

end Silmaril.Numeric.Ieee754.Decimal
