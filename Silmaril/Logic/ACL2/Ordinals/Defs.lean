module

public import Mathlib.SetTheory.Ordinal.Notation

@[expose] public section

namespace Silmaril.Logic.ACL2.Ordinals

/-- The part of the ACL2 value representation relevant to O-P. Every non-natural atom
has the same rejection behavior, so it is represented by `otherAtom`. -/
inductive Encoding where
  | natural (n : Nat)
  | otherAtom
  | cons (car cdr : Encoding)
  deriving DecidableEq, Repr

namespace Encoding

/-- ACL2 MAKE-ORD constructs a dotted pair in the car and attaches the remainder as the cdr. -/
def makeOrd (expt : Encoding) (coeff : Nat) (rest : Encoding) : Encoding :=
  .cons (.cons expt (.natural coeff)) rest

/-- ACL2 O-FIRST-EXPT on well-shaped inputs. -/
def firstExpt : Encoding → Encoding
  | .cons (.cons e _) _ => e
  | _ => .natural 0

/-- Three-way comparison of ordinal encodings. The finite, exponent, coefficient and
remainder cases follow ACL2 O< on O-P inputs. Other shapes have no comparison contract. -/
def cmp : Encoding → Encoding → Ordering
  | .natural m, .natural n => compare m n
  | .natural _, .cons _ _ => .lt
  | .cons _ _, .natural _ => .gt
  | .cons (.cons e (.natural c)) r, .cons (.cons e' (.natural c')) r' =>
      (cmp e e').then ((compare c c').then (cmp r r'))
  | _, _ => .eq

def oLt (x y : Encoding) : Bool := x.cmp y == .lt

/-- ACL2 O-P. The base case is a natural atom. Every infinite term has a nonzero
ordinal exponent, positive natural coefficient, and ordinal remainder with a smaller
leading exponent. A finite remainder has leading exponent zero. -/
def oP : Encoding → Bool
  | .natural _ => true
  | .cons (.cons e (.natural (_c + 1))) r =>
      e.oP && (e != .natural 0) && r.oP && r.firstExpt.oLt e
  | _ => false

/-- Translate a Mathlib ordinal notation into ACL2's encoding. The correspondence
theorems use this map on Cantor normal forms. An exponent-zero term encodes its
coefficient as the final natural atom. -/
def ofNote : ONote → Encoding
  | .zero => .natural 0
  | .oadd e c r =>
    if e = 0 then .natural c.val else makeOrd (ofNote e) c.val (ofNote r)

end Encoding

/-- The domain of ACL2's default well-founded relation, with no bound on the nesting
of exponents or the length of the Cantor normal form. -/
def ValidOrdinal : Type := {x : Encoding // x.oP = true}

namespace ValidOrdinal

/-- Validate a raw measure without coercing an invalid measure to an ordinal. -/
def ofEncoding? (x : Encoding) : Option ValidOrdinal :=
  if h : x.oP = true then some ⟨x, h⟩ else none

def lt (x y : ValidOrdinal) : Prop := x.val.oLt y.val = true

instance (x y : ValidOrdinal) : Decidable (x.lt y) :=
  inferInstanceAs (Decidable (x.val.oLt y.val = true))

/-- The Mathlib notation for an already validated ACL2 ordinal. -/
def toNote (x : ValidOrdinal) : ONote :=
  convert x.val
where
  convert : Encoding → ONote
    | .natural n => ONote.ofNat n
    | .cons (.cons e (.natural (c + 1))) r => .oadd (convert e) c.succPNat (convert r)
    | _ => .zero

end ValidOrdinal
end Silmaril.Logic.ACL2.Ordinals
