module

public import Silmaril.Logic.ACL2.Standard.Objects.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status.Environment

open Standard

/-- ACL2 ALISTP requires cons entries and a NIL tail. Keys and values are arbitrary. -/
def alistP : Object → Bool
  | .cons entry tail => entry.consp && alistP tail
  | atom => decide (atom = .nil)

/-- ACL2 LEN counts the cons spine, including on a dotted list. -/
def len : Object → Nat
  | .cons _ tail => 1 + len tail
  | _ => 0

/-- ACL2 ASSOC-EQUAL uses total CAR, including when an entry is an atom.
It returns the first matching entry itself, or NIL at the end of the spine. -/
def assocEqual (key : Object) : Object → Object
  | .cons entry tail => if key = entry.car then entry else assocEqual key tail
  | _ => .nil

def signedByteP (w : Nat) (v : Object) : Bool :=
  let bound : Int := 2 ^ (w - 1)
  decide (0 < w) && v.integerValue?.any (fun n => decide (-bound ≤ n ∧ n < bound))

/-- RIP-RET-ALISTP tests signed addresses and proper result lists. The address
width is supplied by the translated I48P definition. -/
def ripRetAlistP (width : Nat) : Object → Bool
  | .cons entry tail =>
    entry.consp && signedByteP width entry.car && entry.cdr.trueListp && ripRetAlistP width tail
  | atom => decide (atom = .nil)

end Silmaril.Logic.ACL2.X86Run.Status.Environment
