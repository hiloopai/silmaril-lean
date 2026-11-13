module
public import Silmaril.Formats.Json.Tree.Defs
public import Silmaril.Encoding.Relation
public import Lean.Data.Json.Basic

/-! A format carried by standard JSON has two distinct parsing stages: RFC
JSON bytes become a JSON value, then a schema relates that value to its AST.
The schema can be stated independently of an executable decoder. This module
also adapts existing `Lean.Json` decoders with an explicit Unicode/unique-key
policy; it never silently discards duplicate object members.
-/
@[expose] public section
namespace Silmaril.Formats.Json.Decode

/-- A JSON-level format specification; it need not be functional or executable. -/
abbrev Schema (A : Type) := Silmaril.EncRel (Ast Decimal) A

/-- Compose an application schema with the existing RFC JSON byte parser.
This is relative to `Json.parse?`; it does not assert a separate grammar theorem. -/
def text {A : Type} (schema : Schema A) : Silmaril.EncRel Bytes A :=
  Silmaril.EncRel.comp (Silmaril.EncRel.ofDecoder Json.parse?) schema

def parse? {A : Type} (decode : Ast Decimal → Option A) (bytes : Bytes) : Option A :=
  (Json.parse? bytes).bind decode

/-- The implementation graph, distinct from an independently supplied schema. -/
def graph {A : Type} (decode : Ast Decimal → Option A) : Schema A :=
  Silmaril.EncRel.ofDecoder decode

/-- A decoder satisfying both directions of a JSON-level schema. These fields
are proof obligations, rather than claims implied by executing the decoder. -/
structure Certified (A : Type) (schema : Schema A) where
  decode : Ast Decimal → Option A
  sound : schema.DecoderSound decode
  complete : schema.DecoderComplete decode

/-- Exact decimal conversion to Lean's decimal carrier. Positive exponents
expand the integer mantissa; negative zero is identified with zero. -/
def numberToLean (number : Decimal) : Lean.JsonNumber :=
  let coefficient := if number.exponent ≥ 0 then
      number.coefficient * 10 ^ number.exponent.toNat
    else number.coefficient
  let mantissa : Int := if number.negative then -(coefficient : Int) else coefficient
  ⟨mantissa, if number.exponent ≥ 0 then 0 else number.exponent.natAbs⟩

mutual
  /-- Convert JSON trees for existing Lean decoders. Object order is forgotten;
  duplicate names and non-scalar Unicode strings are rejected at every depth. -/
  def treeToLean? : Tree Decimal → Option Lean.Json
    | .scalar none => some .null
    | .scalar (some (.bool value)) => some (.bool value)
    | .scalar (some (.number value)) => some (.num (numberToLean value))
    | .scalar (some (.string value)) => Lean.Json.str <$> unitsString? value
    | .array values => (fun xs => Lean.Json.arr xs.toArray) <$> arrayToLean? values
    | .object members => Lean.Json.mkObj <$> objectToLean? members
  def arrayToLean? : List (Tree Decimal) → Option (List Lean.Json)
    | [] => some []
    | value :: values => return (← treeToLean? value) :: (← arrayToLean? values)
  def objectToLean? : List (Units × Tree Decimal) → Option (List (String × Lean.Json))
    | [] => some []
    | (key, value) :: members => do
      let name ← unitsString? key
      let value ← treeToLean? value
      let members ← objectToLean? members
      if members.any (fun member => member.1 == name) then none
      else some ((name, value) :: members)
end

def toLean? (value : Ast Decimal) : Option Lean.Json := treeToLean? (Tree.ofAst value)

/-- Lift a schema written against Lean's JSON carrier. The bridge's restrictions
are part of the input contract, independently of the application schema. -/
def fromLean {A : Type} (schema : Silmaril.EncRel Lean.Json A) : Schema A :=
  Silmaril.EncRel.pullPartial toLean? schema

/-- Reuse an existing error-reporting decoder, retaining its successful graph.
The caller may use the original decoder separately when diagnostics are needed. -/
def leanDecode? {A : Type} (decode : Lean.Json → Except String A)
    (value : Ast Decimal) : Option A :=
  (toLean? value).bind fun value => (decode value).toOption

def fromLeanDecoder {A : Type} (decode : Lean.Json → Except String A) : Schema A :=
  fromLean (fun value ast => decode value = .ok ast)

def parseLean? {A : Type} (decode : Lean.Json → Except String A) : Bytes → Option A :=
  parse? (leanDecode? decode)

end Silmaril.Formats.Json.Decode
