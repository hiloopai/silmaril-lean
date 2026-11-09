module
public import Silmaril.Formats.JsonWire.Concrete.Defs
public import Silmaril.Formats.Json.Raw

/-! JSON values use exact decimal numbers and UTF-16 code units. Code units
retain the RFC 8259 grammar's lone surrogate escapes; scalar-Unicode and
portable profiles can reject them explicitly. Object order and duplicates
are observable, reusing Silmaril's indexed raw tree without its extensional
parser's mandatory duplicate rejection.
-/
@[expose] public section
namespace Silmaril.Formats.JsonWire

/-- Exact finite decimal: `(-1)^negative * coefficient * 10^exponent`.
No binary floating-point rounding or exponent expansion occurs when parsing.
The sign of zero is retained; the CST retains the original number spelling.
Trailing coefficient zeroes are permitted, so structural equality is not
equality of mathematical decimal values. -/
structure Decimal where
  negative : Bool
  coefficient : Nat
  exponent : Int
  deriving DecidableEq, Repr

def Decimal.toInt? (d : Decimal) : Option Int :=
  if d.coefficient = 0 then some 0 else
  let magnitude? := if d.exponent ≥ 0 then
      some (d.coefficient * 10 ^ d.exponent.toNat)
    else if d.exponent.natAbs > d.coefficient.repr.length then none
    else let divisor := 10 ^ d.exponent.natAbs
      if d.coefficient % divisor = 0 then some (d.coefficient / divisor) else none
  magnitude?.map fun n => if d.negative then -(n : Int) else n

inductive Number where
  | finite (value : Decimal)
  | infinity (negative : Bool)
  | nan
  deriving DecidableEq, Repr

abbrev Units := List UInt16

inductive Atom (N : Type) where
  | bool (value : Bool)
  | string (value : Units)
  | number (value : N)
  deriving DecidableEq, Repr

abbrev Scalar (N : Type) := Option (Atom N)
abbrev Ast (N : Type := Decimal) := Silmaril.Formats.KeyedRawJson Units (Scalar N)
abbrev Syn (N : Type) := Silmaril.Formats.RawSyn Units (Scalar N)

/-- Syntax dialect and semantic profile are independent choices. -/
inductive Dialect where
  | rfc8259
  /-- RFC syntax plus comments; trailing commas remain errors. -/
  | jsonc
  | json5
  deriving DecidableEq, Repr

inductive Event (N : Type := Decimal) where
  | scalar (value : Scalar N)
  | key (value : Units)
  | startArray | endArray | startObject | endObject
  deriving Repr

inductive TokenKind where
  | whitespace | comment | string | identifier | number | literal
  | arrayOpen | arrayClose | objectOpen | objectClose | comma | colon
  deriving DecidableEq, Repr

abbrev Cst := Concrete (Ast Number) TokenKind

/-- Abstract events preserve ordered object members and duplicate keys. -/
def events {N : Type} : {i : Silmaril.Formats.JsonIx} → Syn N i → List (Event N)
  | _, .scalar s => [.scalar s]
  | _, .list xs => .startArray :: (events xs ++ [.endArray])
  | _, .map xs => .startObject :: (events xs ++ [.endObject])
  | _, .nil => []
  | _, .cons v vs => events v ++ events vs
  | _, .objNil => []
  | _, .objCons k v vs => .key k :: (events v ++ events vs)

def mapNumbers? {A B : Type} (f : A → Option B) :
    {i : Silmaril.Formats.JsonIx} → Syn A i → Option (Syn B i)
  | _, .scalar none => some (.scalar none)
  | _, .scalar (some (.bool b)) => some (.scalar (some (.bool b)))
  | _, .scalar (some (.string s)) => some (.scalar (some (.string s)))
  | _, .scalar (some (.number n)) => (f n).map fun n => .scalar (some (.number n))
  | _, .list xs => (.list ·) <$> mapNumbers? f xs
  | _, .map xs => (.map ·) <$> mapNumbers? f xs
  | _, .nil => some .nil
  | _, .cons v vs => return .cons (← mapNumbers? f v) (← mapNumbers? f vs)
  | _, .objNil => some .objNil
  | _, .objCons k v vs => return .objCons k (← mapNumbers? f v) (← mapNumbers? f vs)

/-- Convert scalar Unicode to its exact UTF-16 code units. -/
def charUnits (c : Char) : Units :=
  if c.toNat < 0x10000 then [UInt16.ofNat c.toNat]
  else let n := c.toNat - 0x10000
    [UInt16.ofNat (0xD800 + n / 0x400), UInt16.ofNat (0xDC00 + n % 0x400)]

def stringUnits (s : String) : Units := s.toList.flatMap charUnits

/-- Reject unpaired surrogates, without rejecting valid surrogate pairs. -/
def scalarUnicode : Units → Bool
  | [] => true
  | u :: us =>
    if 0xD800 ≤ u.toNat && u.toNat ≤ 0xDBFF then
      match us with
      | v :: rest => 0xDC00 ≤ v.toNat && v.toNat ≤ 0xDFFF && scalarUnicode rest
      | [] => false
    else !(0xDC00 ≤ u.toNat && u.toNat ≤ 0xDFFF) && scalarUnicode us

/-- Decode code units only when they denote Unicode scalar values. -/
def unitsChars? : Units → Option (List Char)
  | [] => some []
  | u :: us => do
    if 0xD800 ≤ u.toNat && u.toNat ≤ 0xDBFF then
      match us with
      | v :: rest =>
          if 0xDC00 ≤ v.toNat && v.toNat ≤ 0xDFFF then
            let tail ← unitsChars? rest
            pure (Char.ofNat (0x10000 + (u.toNat - 0xD800) * 0x400 + v.toNat - 0xDC00) :: tail)
          else none
      | [] => none
    else if 0xDC00 ≤ u.toNat && u.toNat ≤ 0xDFFF then none
    else
      let tail ← unitsChars? us
      pure (Char.ofNat u.toNat :: tail)

def unitsString? (us : Units) : Option String := String.ofList <$> unitsChars? us

/-- Look up exactly one member; duplicate matching names are an error.
The base AST itself retains all duplicates. -/
def getMember? {N : Type} (value : Ast N) (name : String) : Option (Ast N) :=
  match value with
  | .map entries => match entries.toEntries.filter (fun entry => entry.1 == stringUnits name) with
    | [(_, value)] => some value
    | _ => none
  | _ => none

def getString? {N : Type} : Ast N → Option String
  | .scalar (some (.string us)) => unitsString? us
  | _ => none

end Silmaril.Formats.JsonWire
