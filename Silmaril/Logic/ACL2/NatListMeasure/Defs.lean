module

public import Silmaril.Logic.ACL2.OrdinalAdmission.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.NatListMeasure

open Ordinals Recursive

/-- ACL2 NFIX factors through the ordinal encoding's projection of non-natural atoms. -/
def nfix : Encoding → Nat
  | .natural n => n
  | _ => 0

/-- ACL2 LEN counts the conses on the cdr spine, including on improper lists. -/
def len : Encoding → Nat
  | .cons _ tail => len tail + 1
  | _ => 0

/-- ACL2 8.7 NAT-LIST-MEASURE. Every ACL2 object has a measure: NFIX is applied
to each car and the final atom, and LEN determines the successive exponents. -/
def ordinalMeasure : Encoding → Encoding
  | .cons head tail => .makeOrd (.natural (len tail + 1)) (nfix head + 1) (ordinalMeasure tail)
  | atom => .natural (nfix atom)

/-- ACL2 NAT-LIST-< compares the outputs of NAT-LIST-MEASURE under O<. -/
def lt (x y : Encoding) : Prop := (ordinalMeasure x).oLt (ordinalMeasure y) = true

instance (x y : Encoding) : Decidable (lt x y) :=
  inferInstanceAs (Decidable ((ordinalMeasure x).oLt (ordinalMeasure y) = true))

/-- An ACL2 two-element proper list, with NIL represented by the non-natural atom. -/
def pair (x y : Encoding) : Encoding := .cons x (.cons y .otherAtom)

variable {S : Signature} {B : Block S} {M : Model S}

/-- Check the actual selected recursive calls against a NAT-LIST-< measure.
The relation has a total domain, so there is no separate input validity premise. -/
def Terminates (B : Block S) (M : Model S) (rank : OrdinalAdmission.Measure B M) : Prop :=
  B.TerminatesBy M (fun next current => lt (rank next) (rank current))

end Silmaril.Logic.ACL2.NatListMeasure
