module

public import Silmaril.Logic.ACL2.Defs
public import Init.Data.Rat.Basic

/-!
# Standard ACL2 logical objects

The object and primitive profile follows stock ACL2 8.7 at
`bc6f4f49e81a0711214a8d91f0d06e0e084d2204`. See
`docs/projects/acl2-standard-objects.md` for the source equations and scope.
-/

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard

/-- A stock ACL2 character is identified by its code in `[0, 256)`. -/
abbrev Character := Fin 256

/-- ACL2 strings are sequences of ACL2 characters. -/
abbrev ByteString := List Character

namespace Character

def ofChar? (c : Char) : Option Character :=
  if h : c.toNat < 256 then some ⟨c.toNat, h⟩ else none

def toChar (c : Character) : Char := Char.ofNat c.val

end Character

namespace ByteString

/-- Convert by character code, rejecting any code outside the ACL2 range. -/
def ofString? (s : String) : Option ByteString := s.toList.mapM Character.ofChar?

/-- Embed each ACL2 character as the Unicode scalar with the same code. -/
def toLeanString (s : ByteString) : String := String.ofList (s.map Character.toChar)

end ByteString

/-- The identity of an already resolved symbol. The package is its home package.
The package environment establishes that the pair is a valid identity in a particular world. -/
structure Symbol where
  package : ByteString
  spelling : ByteString
  package_ne_empty : package ≠ []
  deriving DecidableEq, Repr

namespace Symbol

def toName (s : Symbol) : Name := ⟨s.package.toLeanString, s.spelling.toLeanString⟩

/-- Construct from a resolved `Name`, checking the character range and nonempty home package. -/
def ofName? (n : Name) : Option Symbol := do
  let package ← ByteString.ofString? n.package
  let spelling ← ByteString.ofString? n.symbol
  if h : package ≠ [] then some ⟨package, spelling, h⟩ else none

def nil : Symbol := (ofName? ⟨"COMMON-LISP", "NIL"⟩).get (by decide)
def truth : Symbol := (ofName? ⟨"COMMON-LISP", "T"⟩).get (by decide)
def list : Symbol := (ofName? ⟨"COMMON-LISP", "LIST"⟩).get (by decide)

end Symbol

/-- The stock ACL2 value sort. `Rat` is reduced with positive denominator. A complex
object has nonzero imaginary part, so a rational has only one representation. -/
inductive Object where
  | symbol : Symbol → Object
  | cons : Object → Object → Object
  | character : Character → Object
  | string : ByteString → Object
  | rational : Rat → Object
  | complexRational (real imag : Rat) (imag_ne_zero : imag ≠ 0)
  deriving DecidableEq, Repr

namespace Object

def nil : Object := .symbol Symbol.nil
def truth : Object := .symbol Symbol.truth
def integer (n : Int) : Object := .rational (Rat.ofInt n)

/-- Construct an ACL2 number from exact real and imaginary parts. -/
def ofParts (real imag : Rat) : Object :=
  if h : imag = 0 then .rational real else .complexRational real imag h

def ofBool (b : Bool) : Object := if b then truth else nil

def equal (x y : Object) : Object := ofBool (decide (x = y))

def car : Object → Object
  | .cons x _ => x
  | _ => nil

def cdr : Object → Object
  | .cons _ y => y
  | _ => nil

def consp : Object → Bool
  | .cons .. => true
  | _ => false

def symbolp : Object → Bool
  | .symbol _ => true
  | _ => false

def characterp : Object → Bool
  | .character _ => true
  | _ => false

def stringp : Object → Bool
  | .string _ => true
  | _ => false

def rationalp : Object → Bool
  | .rational _ => true
  | _ => false

def complexRationalp : Object → Bool
  | .complexRational .. => true
  | _ => false

def numberp (x : Object) : Bool := x.rationalp || x.complexRationalp

/-- The integer representation exists exactly when the object is an integral rational. -/
def integerValue? : Object → Option Int
  | .rational q => if q.den = 1 then some q.num else none
  | _ => none

def integerp (x : Object) : Bool := x.integerValue?.isSome

/-- Construct a NIL-terminated list. A raw `cons` can have any object as its cdr. -/
def ofList (xs : List Object) : Object := xs.foldr cons nil

def trueListp : Object → Bool
  | .cons _ tail => tail.trueListp
  | atom => decide (atom = nil)

def append : Object → Object → Object
  | .cons head tail, y => .cons head (tail.append y)
  | _, y => y

def listFix (x : Object) : Object := x.append nil

def symbolName : Object → Object
  | .symbol s => .string s.spelling
  | _ => .string []

def symbolPackageName : Object → Object
  | .symbol s => .string s.package
  | _ => .string []

def charCode : Object → Object
  | .character c => integer c.val
  | _ => integer 0

def codeChar (x : Object) : Object :=
  .character (match x.integerValue? with
    | some n => if h : 0 ≤ n ∧ n.toNat < 256 then ⟨n.toNat, h.2⟩ else 0
    | none => 0)

/-- `make-character-list` preserves the cons spine, replaces non-characters with
code zero, and discards an atomic tail. -/
def characterList : Object → ByteString
  | .cons (.character c) tail => c :: tail.characterList
  | .cons _ tail => 0 :: tail.characterList
  | _ => []

/-- Coerce to a character list only for `COMMON-LISP::LIST`. Every other target
has the logical string-coercion behavior. -/
def coerce (x target : Object) : Object :=
  if target = .symbol Symbol.list then
    match x with
    | .string chars => ofList (chars.map character)
    | _ => nil
  else .string x.characterList

/-- Rational part used by `complex`. Complex objects are outside its rational inputs. -/
def rationalFix : Object → Rat
  | .rational q => q
  | _ => 0

/-- The real component of the number, with logical completion at non-numbers. -/
def real : Object → Rat
  | .rational q => q
  | .complexRational r _ _ => r
  | _ => 0

/-- The imaginary component of the number, with logical completion at non-numbers. -/
def imag : Object → Rat
  | .complexRational _ i _ => i
  | _ => 0

def realpart (x : Object) : Object := .rational x.real
def imagpart (x : Object) : Object := .rational x.imag

def complex (x y : Object) : Object := ofParts x.rationalFix y.rationalFix

def numerator : Object → Object
  | .rational q => integer q.num
  | _ => integer 0

def denominator : Object → Object
  | .rational q => integer q.den
  | _ => integer 1

def fix (x : Object) : Object := if x.numberp then x else integer 0

def ifix (x : Object) : Object := integer (x.integerValue?.getD 0)

/-- The natural rank `nfix` takes a positive integer to its value, and every other
object to zero (including the integer zero). -/
def natRank (x : Object) : Nat := (x.integerValue?.getD 0).toNat

def nfix (x : Object) : Object := integer x.natRank

/-- ACL2 `binary-+`. A non-number contributes zero in both components. -/
def binaryAdd (x y : Object) : Object := ofParts (x.real + y.real) (x.imag + y.imag)

/-- ACL2 `binary-*`. A non-number contributes zero in both components. -/
def binaryMul (x y : Object) : Object :=
  ofParts (x.real * y.real - x.imag * y.imag) (x.real * y.imag + x.imag * y.real)

def unaryMinus (x : Object) : Object := ofParts (-x.real) (-x.imag)

/-- ACL2 unary division returns zero on zero and on non-numbers. -/
def reciprocal (x : Object) : Object :=
  if !x.numberp || x = integer 0 then integer 0
  else
    let norm := x.real * x.real + x.imag * x.imag
    ofParts (x.real / norm) (-x.imag / norm)

/-- ACL2 `<` compares the rational components lexicographically after logical completion. -/
def less (x y : Object) : Object :=
  ofBool (decide (x.real < y.real ∨ (x.real = y.real ∧ x.imag < y.imag)))

/-- Logical `zp` is NIL exactly on positive integer objects. -/
def zp (x : Object) : Object :=
  match x.integerValue? with
  | some n => ofBool (decide (n ≤ 0))
  | none => truth

def decrement (x : Object) : Object := x.binaryAdd (integer (-1))

/-- ACL2 8.7 `acl2-count`, used as a natural measure. -/
def acl2Count : Object → Nat
  | .cons head tail => 1 + head.acl2Count + tail.acl2Count
  | .rational q => rationalCount q
  | .complexRational r i _ => 1 + rationalCount r + rationalCount i
  | .string s => s.length
  | _ => 0
where
  rationalCount (q : Rat) : Nat := if q.den = 1 then q.num.natAbs else q.num.natAbs + q.den

end Object

/-- The canonical standard objects instantiate the existing core without changing its terms. -/
def objectPrimitives : Primitives where
  Value := Object
  nil := Object.nil
  truth := Object.truth
  cons := Object.cons
  car := Object.car
  cdr := Object.cdr
  consp := Object.consp
  truth_ne_nil := by decide
  consp_nil := rfl
  consp_truth := rfl
  consp_cons _ _ := rfl
  car_cons _ _ := rfl
  cdr_cons _ _ := rfl
  car_atom x h := by cases x <;> first | rfl | contradiction
  cdr_atom x h := by cases x <;> first | rfl | contradiction

/-- Interpret an existing arity-checked signature over standard objects. -/
def objectModel (S : Signature) (interpret : ∀ {n}, S.Symbol n → (Fin n → Object) → Object) :
    Model S := ⟨objectPrimitives, interpret⟩

end Silmaril.Logic.ACL2.Standard
