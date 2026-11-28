module

public import Silmaril.Logic.ACL2.Standard.BitSelection.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Object

/-- The common shape of a generated fixed-width object projection. The input
is fixed to the containing width before selecting the field. -/
def fixedWidthProjection (container width offset : Nat) (x : Object) : Object :=
  partSelectWidthLow (loghead (integer container) x) (integer width) (integer offset)

def prefixesFix (x : Object) : Object := loghead (integer 52) x

def prefixesAdr (x : Object) : Object := fixedWidthProjection 52 8 36 x

def prefixesNum (x : Object) : Object := fixedWidthProjection 52 4 0 x

def prefixesNxt (x : Object) : Object := fixedWidthProjection 52 8 44 x

end Silmaril.Logic.ACL2.Standard.Object
