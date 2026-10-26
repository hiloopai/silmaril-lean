module

public import Silmaril.Numeric.DecimalText
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exact decimal parser laws

Digit concatenation, decimal-point placement and exponent notation are proved
against the executable scanner and Lean's actual natural-number rendering.
-/

@[expose] public section

namespace Silmaril.Numeric.DecimalText

def Digits (characters : List Char) : Prop := ∀ c ∈ characters, c.isDigit = true

theorem Digits.append {left right : List Char} (hl : Digits left) (hr : Digits right) :
    Digits (left ++ right) := by
  intro c member
  rcases List.mem_append.mp member with member | member
  · exact hl c member
  · exact hr c member

theorem Digits.take {characters : List Char} (valid : Digits characters) (count : Nat) :
    Digits (characters.take count) := fun c member => valid c (List.mem_of_mem_take member)

theorem Digits.drop {characters : List Char} (valid : Digits characters) (count : Nat) :
    Digits (characters.drop count) := fun c member => valid c (List.mem_of_mem_drop member)

theorem digits_repr (number : Nat) : Digits (toString number).toList := by
  intro c member
  rw [Nat.toString_eq_repr, Nat.toList_repr] at member
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) member

theorem digits_zeros (count : Nat) : Digits (List.replicate count '0') := by
  intro c member
  have equal := List.eq_of_mem_replicate member
  subst c
  decide

@[simp] theorem digitsValue_repr (number : Nat) : digitsValue (toString number).toList = number := by
  simp only [digitsValue, Nat.toString_eq_repr, Nat.toList_repr, Nat.ofDigitChars_ten_toDigits]

@[simp] theorem digitsValue_zeros (count : Nat) : digitsValue (List.replicate count '0') = 0 := by
  simp only [digitsValue, Nat.ofDigitChars_replicate_zero, Nat.mul_zero]

theorem digitsValue_append (left right : List Char) :
    digitsValue (left ++ right) = 10 ^ right.length * digitsValue left + digitsValue right := by
  simp only [digitsValue, Nat.ofDigitChars_append]
  rw [Nat.ofDigitChars_eq_ofDigitChars_zero]

theorem parseNat_digits (characters : List Char) (valid : Digits characters) (nonempty : characters ≠ []) :
    parseNat characters = some (digitsValue characters) := by
  have all : characters.all Char.isDigit = true := List.all_eq_true.mpr valid
  simp [parseNat, all, nonempty]

/-- Reading a valid digit prefix updates the ordinary base-ten accumulator
and the fractional count, then continues at the exact remaining suffix. -/
theorem scan_digits_append (digits rest : List Char) (valid : Digits digits)
    (coefficient fractional : Nat) (point seen : Bool) :
    scan (digits ++ rest) coefficient fractional point seen =
      scan rest (Nat.ofDigitChars 10 digits coefficient)
        (fractional + if point then digits.length else 0) point (seen || !digits.isEmpty) := by
  induction digits generalizing coefficient fractional seen with
  | nil => simp only [List.nil_append, Nat.ofDigitChars_nil, List.length_nil, ite_self, Nat.add_zero,
      List.isEmpty_nil, Bool.not_true, Bool.or_false]
  | cons c digits ih =>
    have digit := valid c (by simp)
    have remaining : Digits digits := fun d member => valid d (by simp [member])
    simp only [List.cons_append, scan, digit, ↓reduceIte, Nat.ofDigitChars_cons]
    rw [ih remaining]
    cases point <;> simp
    congr 1
    omega

@[simp] theorem scan_dot (rest : List Char) (coefficient fractional : Nat) (seen : Bool) :
    scan ('.' :: rest) coefficient fractional false seen = scan rest coefficient fractional true seen := by
  simp [scan, Char.isDigit]

@[simp] theorem scan_exponent (rest : List Char) (coefficient fractional : Nat) (point : Bool) :
    scan ('e' :: rest) coefficient fractional point true =
      (parseExponent rest).map (finish coefficient fractional) := by
  simp [scan, Char.isDigit]

theorem scan_integer (digits : List Char) (valid : Digits digits) (nonempty : digits ≠ []) :
    scan digits 0 0 false false = some (finish (digitsValue digits) 0 0) := by
  have result := scan_digits_append digits [] valid 0 0 false false
  simpa [scan, nonempty, digitsValue] using result

theorem scan_fixed (before after : List Char) (beforeValid : Digits before) (afterValid : Digits after)
    (nonempty : before ≠ []) :
    scan (before ++ '.' :: after) 0 0 false false =
      some (finish (digitsValue (before ++ after)) after.length 0) := by
  rw [scan_digits_append before _ beforeValid]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.false_or]
  have seen : (!before.isEmpty) = true := by simp [nonempty]
  rw [seen, scan_dot]
  have result := scan_digits_append after [] afterValid (Nat.ofDigitChars 10 before 0) 0 true true
  simp only [List.append_nil, ↓reduceIte, Nat.zero_add, Bool.true_or, scan] at result
  simpa only [digitsValue, Nat.ofDigitChars_append] using result

theorem scan_scientific (before after exponent : List Char) (beforeValid : Digits before)
    (afterValid : Digits after) (nonempty : before ≠ []) {power : Int}
    (parsed : parseExponent exponent = some power) :
    scan (before ++ '.' :: (after ++ 'e' :: exponent)) 0 0 false false =
      some (finish (digitsValue (before ++ after)) after.length power) := by
  rw [scan_digits_append before _ beforeValid]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.false_or]
  have seen : (!before.isEmpty) = true := by simp [nonempty]
  rw [seen, scan_dot, scan_digits_append after _ afterValid]
  simp only [↓reduceIte, Nat.zero_add, Bool.true_or, scan_exponent, parsed, Option.map_some,
    digitsValue, Nat.ofDigitChars_append]

theorem scan_integer_scientific (digits exponent : List Char) (valid : Digits digits)
    (nonempty : digits ≠ []) {power : Int} (parsed : parseExponent exponent = some power) :
    scan (digits ++ 'e' :: exponent) 0 0 false false = some (finish (digitsValue digits) 0 power) := by
  rw [scan_digits_append digits _ valid]
  have seen : (!digits.isEmpty) = true := by simp [nonempty]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.false_or, seen,
    scan_exponent, parsed, Option.map_some, digitsValue]

/-- Successful unsigned scanning produces the same finite parse. The scanner
rejects initial sign characters, so this does not conflate signed and unsigned
zero representations. -/
theorem parseFinite_of_scan (input : List Char) (value : ℚ)
    (scanned : scan input 0 0 false false = some value) :
    parseFinite input = some ⟨false, value⟩ := by
  unfold parseFinite
  split
  next rest => simp [scan, Char.isDigit] at scanned
  next rest => simp [scan, Char.isDigit] at scanned
  next rest => rw [scanned]; rfl

/-- The special spelling cases are disjoint from successful finite parsing. -/
theorem parse_of_parseFinite (text : String) (value : Finite)
    (parsed : parseFinite text.toList = some value) : parse text = some (.finite value) := by
  unfold parse
  split_ifs with nan infinity negativeInfinity
  · have same : text = "nan" := by simpa using nan
    subst text
    simp [parseFinite, scan, Char.isDigit] at parsed
  · have same : text = "inf" ∨ text = "+inf" := by simpa using infinity
    rcases same with rfl | rfl <;> simp [parseFinite, scan, Char.isDigit] at parsed
  · have same : text = "-inf" := by simpa using negativeInfinity
    subst text
    simp [parseFinite, scan, Char.isDigit] at parsed
  · rw [parsed]; rfl

theorem parse_unsigned_of_scan (text : String) (value : ℚ)
    (scanned : scan text.toList 0 0 false false = some value) :
    parse text = some (.finite ⟨false, value⟩) :=
  parse_of_parseFinite text _ (parseFinite_of_scan _ _ scanned)

theorem parse_negative_of_scan (text : String) (value : ℚ)
    (scanned : scan text.toList 0 0 false false = some value) :
    parse ("-" ++ text) = some (.finite ⟨true, value⟩) := by
  apply parse_of_parseFinite
  rw [String.toList_append]
  change (scan text.toList 0 0 false false).map (Finite.mk true) = _
  rw [scanned]
  rfl

end Silmaril.Numeric.DecimalText
