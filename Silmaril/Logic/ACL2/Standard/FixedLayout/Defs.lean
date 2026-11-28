module

public import Silmaril.Logic.ACL2.Standard.Pure.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Object

/-- The length of the cons spine, including for a dotted list. -/
def spineLength : Object → Nat
  | .cons _ tail => tail.spineLength + 1
  | _ => 0

def len (x : Object) : Object := integer x.spineLength

/-- Read by a natural position using the total CAR and CDR. -/
def readAt : Nat → Object → Object
  | 0, x => x.car
  | i + 1, x => readAt i x.cdr

/-- Write by a natural position. Missing cells are filled with NIL. -/
def writeAt : Nat → Object → Object → Object
  | 0, value, x => .cons value x.cdr
  | i + 1, value, x => .cons x.car (writeAt i value x.cdr)

/-- ACL2 UPDATE-NTH uses slot zero when the index is negative or nonintegral. -/
def updateNth (index value x : Object) : Object := writeAt index.natRank value x

/-- Logical MAKE-LIST-AC, with the original object as the final tail. -/
def makeListAc (n value acc : Object) : Object :=
  (List.replicate n.natRank value).foldl (fun tail head => .cons head tail) acc

/-- Recognize proper lists whose cells satisfy the given predicate. -/
def listAll (p : Object → Bool) : Object → Bool
  | .cons head tail => p head && listAll p tail
  | atom => decide (atom = nil)

end Silmaril.Logic.ACL2.Standard.Object

namespace Silmaril.Logic.ACL2.Standard.FixedLayout.Toy

open Object

def encode (scalar : Int) (cells : List Int) : Object :=
  ofList [integer scalar, ofList (cells.map integer)]

def initial : Object := encode (-2) [7, 7, 7]

def cellsP (x : Object) : Object := ofBool (x.listAll integerp)

def recognizes (x : Object) : Bool :=
  x.trueListp && decide (x.spineLength = 2) && x.car.integerp &&
    x.cdr.car.listAll integerp && decide (x.cdr.car.spineLength = 3)

def recognizer (x : Object) : Object := ofBool (recognizes x)

def readScalar (x : Object) : Object := x.car

def writeScalar (value x : Object) : Object := writeAt 0 value x

def readCell (index x : Object) : Object := index.mvNth x.cdr.car

def writeCell (index value x : Object) : Object := writeAt 1 (index.updateNth value x.cdr.car) x

end Silmaril.Logic.ACL2.Standard.FixedLayout.Toy
