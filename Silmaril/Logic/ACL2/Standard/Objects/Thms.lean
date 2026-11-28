module

public import Silmaril.Logic.ACL2.Standard.Objects.Defs
import Silmaril.Proofs.Logic.ACL2.Standard.Objects

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard

open Proofs.Logic.ACL2.Standard in
@[simp] theorem ByteString.ofString?_toLeanString (s : ByteString) :
    ByteString.ofString? s.toLeanString = some s := Objects.byteString_roundtrip s

open Proofs.Logic.ACL2.Standard in
theorem ByteString.toLeanString_ofString? {s : String} {bs : ByteString}
    (h : ByteString.ofString? s = some bs) : bs.toLeanString = s := Objects.byteString_ofString h

open Proofs.Logic.ACL2.Standard in
@[simp] theorem Symbol.ofName?_toName (s : Symbol) : Symbol.ofName? s.toName = some s :=
  Objects.symbol_roundtrip s

open Proofs.Logic.ACL2.Standard in
theorem Symbol.toName_ofName? {n : Name} {s : Symbol} (h : Symbol.ofName? n = some s) :
    s.toName = n := Objects.symbol_toName h

theorem Symbol.toName_injective : Function.Injective Symbol.toName := by
  intro s t h
  simpa only [Symbol.ofName?_toName, Option.some.injEq] using congrArg Symbol.ofName? h

namespace Object

open Proofs.Logic.ACL2.Standard

@[simp] theorem truth_ne_nil : truth ≠ nil := objectPrimitives.truth_ne_nil
@[simp] theorem nil_ne_truth : nil ≠ truth := Ne.symm truth_ne_nil

@[simp] theorem car_cons (x y : Object) : (cons x y).car = x := rfl
@[simp] theorem cdr_cons (x y : Object) : (cons x y).cdr = y := rfl
@[simp] theorem consp_cons (x y : Object) : (cons x y).consp = true := rfl

theorem car_atom {x : Object} (h : x.consp = false) : x.car = nil := objectPrimitives.car_atom x h
theorem cdr_atom {x : Object} (h : x.consp = false) : x.cdr = nil := objectPrimitives.cdr_atom x h

theorem cons_car_cdr (x : Object) : cons x.car x.cdr = if x.consp then x else cons nil nil :=
  Objects.cons_car_cdr x

@[simp] theorem equal_eq_truth (x y : Object) : x.equal y = truth ↔ x = y :=
  Objects.equal_eq_truth x y

@[simp] theorem equal_eq_nil (x y : Object) : x.equal y = nil ↔ x ≠ y := Objects.equal_eq_nil x y

@[simp] theorem append_cons (x y z : Object) : (cons x y).append z = cons x (y.append z) := rfl
@[simp] theorem append_nil_left (x : Object) : nil.append x = x := rfl

theorem append_atom {x : Object} (h : x.consp = false) (y : Object) : x.append y = y :=
  Objects.append_atom h y

theorem append_assoc (x y z : Object) : (x.append y).append z = x.append (y.append z) :=
  Objects.append_assoc x y z

/-- Appending NIL removes any atomic tail other than NIL. -/
theorem append_nil_right (x : Object) : x.append nil = x.listFix := rfl

theorem listFix_of_trueListp {x : Object} (h : x.trueListp = true) : x.listFix = x :=
  Objects.listFix_of_trueListp h

@[simp] theorem trueListp_listFix (x : Object) : x.listFix.trueListp = true :=
  Objects.trueListp_listFix x

theorem append_nil_of_trueListp {x : Object} (h : x.trueListp = true) : x.append nil = x :=
  listFix_of_trueListp h

theorem symbolName_of_nonsymbol {x : Object} (h : x.symbolp = false) :
    x.symbolName = .string [] := Objects.symbolName_of_nonsymbol h

theorem symbolPackageName_of_nonsymbol {x : Object} (h : x.symbolp = false) :
    x.symbolPackageName = .string [] := Objects.symbolPackageName_of_nonsymbol h

theorem charCode_of_noncharacter {x : Object} (h : x.characterp = false) :
    x.charCode = integer 0 := Objects.charCode_of_noncharacter h

theorem integerValue?_eq_some_iff (x : Object) (n : Int) :
    x.integerValue? = some n ↔ x = integer n := Objects.integerValue?_eq_some_iff x n

@[simp] theorem codeChar_charCode (c : Character) : (character c).charCode.codeChar = character c :=
  Objects.codeChar_charCode c

theorem codeChar_of_outside {n : Int} (h : n < 0 ∨ 256 ≤ n) :
    (integer n).codeChar = character 0 := Objects.codeChar_of_outside h

theorem codeChar_of_noninteger {x : Object} (h : x.integerValue? = none) :
    x.codeChar = character 0 := by simp [codeChar, h]

theorem coerceList_roundtrip (s : ByteString) {target : Object} (h : target ≠ .symbol Symbol.list) :
    ((string s).coerce (.symbol Symbol.list)).coerce target = string s :=
  Objects.coerceList_roundtrip s target h

theorem coerce_of_other_target (x target : Object) (h : target ≠ .symbol Symbol.list) :
    x.coerce target = string x.characterList := by simp [coerce, h]

theorem coerceList_of_nonstring {x : Object} (h : x.stringp = false) :
    x.coerce (.symbol Symbol.list) = nil := by
  cases x <;> simp_all [coerce, stringp]

@[simp] theorem ofParts_zero (r : Rat) : ofParts r 0 = rational r := by simp [ofParts]
@[simp] theorem real_ofParts (r i : Rat) : (ofParts r i).real = r := Objects.real_ofParts r i
@[simp] theorem imag_ofParts (r i : Rat) : (ofParts r i).imag = i := Objects.imag_ofParts r i

theorem ofParts_real_imag (x : Object) : ofParts x.real x.imag = x.fix := Objects.ofParts_real_imag x

theorem numerator_of_nonrational {x : Object} (h : x.rationalp = false) :
    x.numerator = integer 0 := by
  cases x <;> first | rfl | contradiction

theorem denominator_of_nonrational {x : Object} (h : x.rationalp = false) :
    x.denominator = integer 1 := by
  cases x <;> first | rfl | contradiction

theorem binaryAdd_of_nonnumeric_left {x : Object} (h : x.numberp = false) (y : Object) :
    x.binaryAdd y = y.fix := Objects.binaryAdd_of_nonnumeric_left h y

theorem binaryAdd_of_nonnumeric_right (x : Object) {y : Object} (h : y.numberp = false) :
    x.binaryAdd y = x.fix := Objects.binaryAdd_of_nonnumeric_right x h

theorem binaryMul_of_nonnumeric_left {x : Object} (h : x.numberp = false) (y : Object) :
    x.binaryMul y = integer 0 := Objects.binaryMul_of_nonnumeric_left h y

theorem binaryMul_of_nonnumeric_right (x : Object) {y : Object} (h : y.numberp = false) :
    x.binaryMul y = integer 0 := Objects.binaryMul_of_nonnumeric_right x h

theorem unaryMinus_of_nonnumeric {x : Object} (h : x.numberp = false) :
    x.unaryMinus = integer 0 := Objects.unaryMinus_of_nonnumeric h

theorem reciprocal_of_nonnumeric {x : Object} (h : x.numberp = false) :
    x.reciprocal = integer 0 := by simp [reciprocal, h]

@[simp] theorem reciprocal_zero : (integer 0).reciprocal = integer 0 := by decide

theorem less_of_nonnumeric_left {x : Object} (h : x.numberp = false) (y : Object) :
    x.less y = (integer 0).less y := Objects.less_of_nonnumeric_left h y

theorem less_of_nonnumeric_right (x : Object) {y : Object} (h : y.numberp = false) :
    x.less y = x.less (integer 0) := Objects.less_of_nonnumeric_right x h

theorem zp_eq_nil_iff (x : Object) : x.zp = nil ↔ ∃ n : Int, 0 < n ∧ x = integer n :=
  Objects.zp_eq_nil_iff x

@[simp] theorem decrement_integer (n : Int) : (integer n).decrement = integer (n - 1) :=
  Objects.decrement_integer n

/-- A negative `zp` branch licenses the natural rank decrease for `(+ x -1)`. -/
theorem natRank_decrement_lt {x : Object} (h : x.zp = nil) : x.decrement.natRank < x.natRank :=
  Objects.natRank_decrement_lt h

theorem acl2Count_cdr_lt {x : Object} (h : x.consp = true) : x.cdr.acl2Count < x.acl2Count :=
  Objects.acl2Count_cdr_lt h

end Object

theorem objectPrimitives_equal (x y : Object) : objectPrimitives.equal x y = x.equal y := rfl

end Silmaril.Logic.ACL2.Standard
