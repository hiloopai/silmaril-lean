module

public import Silmaril.Logic.ACL2.Standard.Objects.Defs
public import Mathlib.Data.Int.Bitwise

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Object

/-- The integer payload used by ACL2's `ifix`. -/
def integerFix (x : Object) : Int := x.integerValue?.getD 0

/-- ACL2 `BINARY-LOGAND`, on integers with unbounded sign extension. -/
def binaryLogand (x y : Object) : Object := integer (Int.land x.integerFix y.integerFix)

/-- ACL2 `BINARY-LOGIOR`, on integers with unbounded sign extension. -/
def binaryLogior (x y : Object) : Object := integer (Int.lor x.integerFix y.integerFix)

/-- ACL2 `BINARY-LOGXOR`, on integers with unbounded sign extension. -/
def binaryLogxor (x y : Object) : Object := integer (Int.xor x.integerFix y.integerFix)

/-- Value semantics of the ACL2 `LOGAND` macro, including the zero- and one-argument cases. -/
def logand : List Object → Object
  | [] => integer (-1)
  | x :: tail =>
    match tail with
    | [] => x
    | _ :: _ => x.binaryLogand (logand tail)
termination_by structural args => args

/-- Value semantics of the ACL2 `LOGIOR` macro. -/
def logior : List Object → Object
  | [] => integer 0
  | x :: tail =>
    match tail with
    | [] => x
    | _ :: _ => x.binaryLogior (logior tail)
termination_by structural args => args

/-- Value semantics of the ACL2 `LOGXOR` macro. -/
def logxor : List Object → Object
  | [] => integer 0
  | x :: tail =>
    match tail with
    | [] => x
    | _ :: _ => x.binaryLogxor (logxor tail)
termination_by structural args => args

/-- ACL2 `LOGNOT` complements every bit, including the unbounded sign extension. -/
def lognot (x : Object) : Object := integer (Int.lnot x.integerFix)

/-- ACL2 `ASH`. Right shifts round toward negative infinity. A noninteger count acts as zero. -/
def ash (x count : Object) : Object :=
  let c := count.integerFix
  integer (if 0 ≤ c then Int.shiftLeft x.integerFix c.toNat
    else Int.shiftRight x.integerFix (-c).toNat)

/-- ACL2 `LOGBITP` uses `nfix` on the index and `ifix` on the integer being tested. -/
def logbitp (index x : Object) : Object := ofBool (x.integerFix.testBit index.natRank)

/-- ACL2 `INTEGER-LENGTH` counts the bits of `x` if nonnegative, or of `-1 - x` otherwise. -/
def integerLength (x : Object) : Object :=
  integer (match x.integerFix with
    | .ofNat n | .negSucc n => Int.ofNat n.size)

end Silmaril.Logic.ACL2.Standard.Object
