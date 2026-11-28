module

public import Silmaril.Logic.ACL2.Standard.IntegerBits.Defs
import Silmaril.Proofs.Logic.ACL2.Standard.IntegerBits

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Object

open Proofs.Logic.ACL2.Standard

@[simp] theorem integerFix_integer (i : Int) : (integer i).integerFix = i := rfl

theorem integerFix_of_noninteger {x : Object} (h : x.integerValue? = none) :
    x.integerFix = 0 := by simp [integerFix, h]

theorem integer_integerFix (x : Object) : integer x.integerFix = x.ifix := rfl

/-- The digit step of ACL2's `BINARY-LOGAND`. It also holds in the base cases. -/
theorem binaryLogand_recurrence (x y : Object) :
    x.binaryLogand y = integer
      (2 * ((integer (x.integerFix / 2)).binaryLogand (integer (y.integerFix / 2))).integerFix +
        (if x.integerFix % 2 = 1 ∧ y.integerFix % 2 = 1 then 1 else 0)) :=
  congrArg integer (IntegerBits.land_recurrence x.integerFix y.integerFix)

theorem binaryLogand_zero_left {x : Object} (h : x.integerFix = 0) (y : Object) :
    x.binaryLogand y = integer 0 := by simp [binaryLogand, h, IntegerBits.land_zero_left]

theorem binaryLogand_zero_right (x : Object) {y : Object} (h : y.integerFix = 0) :
    x.binaryLogand y = integer 0 := by simp [binaryLogand, h, IntegerBits.land_zero_right]

@[simp] theorem binaryLogand_neg_one_left (x : Object) :
    (integer (-1)).binaryLogand x = x.ifix := by
  simp [binaryLogand, IntegerBits.land_neg_one_left, integer_integerFix]

@[simp] theorem binaryLogand_neg_one_right (x : Object) :
    x.binaryLogand (integer (-1)) = x.ifix := by
  simp [binaryLogand, IntegerBits.land_neg_one_right, integer_integerFix]

/-- ACL2's arithmetic equation for `LOGNOT`, including `ifix` on nonintegers. -/
theorem lognot_eq (x : Object) : x.lognot = integer (-x.integerFix - 1) := IntegerBits.lognot_eq x

/-- The defining ACL2 equation for `BINARY-LOGIOR` on all logical objects. -/
theorem binaryLogior_eq (x y : Object) : x.binaryLogior y = (x.lognot.binaryLogand y.lognot).lognot :=
  IntegerBits.logior_eq x y

/-- The `LOGEQV` and `LOGORC1` definitions expanded in ACL2's `BINARY-LOGXOR`. -/
theorem binaryLogxor_eq (x y : Object) : x.binaryLogxor y =
    ((x.lognot.binaryLogior y).binaryLogand (y.lognot.binaryLogior x)).lognot :=
  IntegerBits.logxor_eq x y

/-- The two cases of `floor (* (ifix x) (expt 2 count)) 1` in stock ACL2. -/
theorem ash_eq (x count : Object) : x.ash count = integer
    (if 0 ≤ count.integerFix then x.integerFix * 2 ^ count.integerFix.toNat
     else x.integerFix / 2 ^ (-count.integerFix).toNat) := IntegerBits.ash_eq x count

theorem ash_zero_count (x : Object) {count : Object} (h : count.integerFix = 0) :
    x.ash count = x.ifix := by simp [ash_eq, h, integer_integerFix]

/-- ACL2 tests the parity of the floor quotient using `nfix` on the index. -/
theorem logbitp_eq (index x : Object) : index.logbitp x =
    ofBool (decide (x.integerFix / 2 ^ index.natRank % 2 = 1)) := IntegerBits.logbitp_eq index x

theorem integerLength_of_noninteger {x : Object} (h : x.integerValue? = none) :
    x.integerLength = integer 0 := by rw [integerLength, integerFix_of_noninteger h]; rfl

@[simp] theorem integerLength_zero : (integer 0).integerLength = integer 0 := rfl
@[simp] theorem integerLength_neg_one : (integer (-1)).integerLength = integer 0 := rfl

/-- The non-base branch of the ACL2 `INTEGER-LENGTH` recurrence, with floor division. -/
theorem integerLength_recurrence (n : Int) (hz : n ≠ 0) (hs : n ≠ -1) :
    (integer n).integerLength = integer (1 + (integer (n / 2)).integerLength.integerFix) :=
  IntegerBits.integerLength_recurrence n hz hs

end Silmaril.Logic.ACL2.Standard.Object
