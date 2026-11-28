module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.FixedLayout.Schema

open Object

/-- Logical slot types in the supported fixed-layout profile. -/
inductive Slot where
  | scalar (initial : Int)
  | array (size : Nat) (initial : Int)

def Slot.accepts : Slot → Object → Bool
  | .scalar _, x => x.integerp
  | .array size _, x => x.listAll integerp && decide (x.spineLength = size)

def Slot.initialObject : Slot → Object
  | .scalar initial => integer initial
  | .array size initial => ofList (List.replicate size (integer initial))

def integerListP (x : Object) : Object := ofBool (x.listAll integerp)

def initial (layout : List Slot) : Object := ofList (layout.map Slot.initialObject)

/-- Check each declared position. The outer shape is checked separately. -/
def fieldsAccept : List Slot → Object → Bool
  | [], _ => true
  | slot :: layout, x => slot.accepts x.car && fieldsAccept layout x.cdr

def recognizes (layout : List Slot) (x : Object) : Bool :=
  x.trueListp && decide (x.spineLength = layout.length) && fieldsAccept layout x

def recognizer (layout : List Slot) (x : Object) : Object := ofBool (recognizes layout x)

/-- Slot numbers are natural. The logical cell index uses ACL2's natural fix. -/
def readCell (slot : Nat) (index x : Object) : Object := index.mvNth (readAt slot x)

def writeCell (slot : Nat) (index value x : Object) : Object :=
  writeAt slot (index.updateNth value (readAt slot x)) x

end Silmaril.Logic.ACL2.Standard.FixedLayout.Schema
