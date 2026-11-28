module

public import Silmaril.Logic.ACL2.X86Run.Status.RecordDefs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status.Tlb

open Standard

structure Layout where
  marker : Object
  keyWidth : Nat
  pageWidth : Nat
  modeWidth : Nat
  modeOffset : Nat
  maxMode : Nat

def selectedBits (width offset key : Nat) : Nat :=
  (key / 2 ^ offset) % 2 ^ width

def keyP (l : Layout) (x : Object) : Bool := unsignedByteP l.keyWidth x

/-- The integer bit selection is reached only after the key passes the unsigned check. -/
def goodKeyP (l : Layout) (x : Object) : Bool :=
  keyP l x && decide (selectedBits l.modeWidth l.modeOffset x.natRank ≤ l.maxMode)

def entryP (l : Layout) : Object → Bool
  | .cons key page => goodKeyP l key && unsignedByteP l.pageWidth page
  | _ => false

/-- The logical TLB is a cons spine terminated by the exported marker. -/
def recognizes (l : Layout) : Object → Bool
  | .cons entry tail => entryP l entry && recognizes l tail
  | x => decide (x = l.marker)

end Silmaril.Logic.ACL2.X86Run.Status.Tlb
