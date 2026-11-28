module

public import Silmaril.Logic.ACL2.Standard.IntegerBits.Defs
public import Silmaril.Logic.ACL2.Standard.Quotient.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Object

/-- Logical LOGHEAD. A width with natural fix zero has modulus one. -/
def loghead (width x : Object) : Object := integer (x.integerFix % (2 ^ width.natRank : Nat))

/-- Logical LOGTAIL, using floor division by a positive power of two. -/
def logtail (low x : Object) : Object := integer (x.integerFix / (2 ^ low.natRank : Nat))

/-- The width expression of the low/high declaration, before LOGHEAD fixes it. -/
def selectionWidth (low high : Object) : Object :=
  (integer 1).binaryAdd (high.binaryAdd low.unaryMinus)

def partSelectWidthLow (x width low : Object) : Object := loghead width (logtail low x)

def partSelectLowHigh (x low high : Object) : Object :=
  partSelectWidthLow x (selectionWidth low high) low

end Silmaril.Logic.ACL2.Standard.Object

namespace Silmaril.Logic.ACL2.Standard.BitSelection.Source

/-- ACL2 FLOOR on integer operands, using its rational quotient definition. -/
def floorIntegers (x divisor : Int) : Object :=
  .integer (Quotient.floorRatio (Rat.divInt x divisor))

/-- ACL2 MOD on integer operands, following the defining FLOOR equation. -/
def modIntegers (x divisor : Int) : Object :=
  .integer (x - (floorIntegers x divisor).integerFix * divisor)

end Silmaril.Logic.ACL2.Standard.BitSelection.Source
