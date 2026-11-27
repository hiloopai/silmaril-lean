module

public import Silmaril.Formats.Csv.Typed.Utf8.Defs

/-! Opt-in UTF-8 typed CSV decoding with a retained data-row budget. -/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed.Utf8.Bounded

open Silmaril.Formats.Csv.Internal (readField comma cr lf)
open Silmaril.Formats.Csv.Typed.Internal (importRow)

inductive Error where
  | csv (reason : Typed.Error)
  | rowLimit
  deriving DecidableEq, Repr

namespace Internal

/-- Parse fields of one logical record. Follow commas using the shared
field reader and return at CRLF or at the end of the input. -/
def readRawRow (wire : Bytes) : Option (Row × Bytes) := do
  let field ← readField wire .utf8Bytes
  have _bound := field.rest_le
  match _h : field.rest with
  | [] => some ([field.field], [])
  | b :: bs =>
    if b = comma then
      let (rest, suffix) ← readRawRow bs
      some (field.field :: rest, suffix)
    else if b = cr then
      match bs with
      | c :: rest => if c = lf then some ([field.field], rest) else none
      | [] => none
    else none
termination_by wire.length
decreasing_by simp_all only [List.length_cons]; omega

/-- Validate one unescaped UTF-8 row using the existing wire profile. -/
def readRow (wire : Bytes) : Option (Row × Bytes) := do
  let (row, rest) ← readRawRow wire
  if Csv.Utf8.rowsOK [row] then some (row, rest) else none

variable {Kind : Type*} {Value : Kind → Type*}

def readBody (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind)) :
    Nat → Bytes → Except Error (Table schema Value)
  | _, [] => .ok []
  | 0, _ :: _ => .error .rowLimit
  | remaining + 1, b :: bs =>
    match readRow (b :: bs) with
    | none => .error (.csv .malformedWire)
    | some (raw, rest) =>
      match importRow schema codecs raw with
      | .error reason => .error (.csv reason)
      | .ok row => (readBody schema codecs remaining rest).map (row :: ·)

end Internal

variable {Kind : Type*} {Value : Kind → Type*}

/-- Read one header, then validate and retain at most `maxRows` data
rows. At the bound, a nonempty suffix gives `rowLimit` before parsing
another record. A result table is returned only at the end of input. -/
def decode (maxRows : Nat) (schema : Schema Kind)
    (codecs : (kind : Kind) → CellCodec (Value kind)) (wire : Bytes) :
    Except Error (Table schema Value) :=
  match wire with
  | [] => .error (.csv .missingHeader)
  | b :: bs =>
    match Internal.readRow (b :: bs) with
    | none => .error (.csv .malformedWire)
    | some (raw, rest) =>
      if raw = header schema then Internal.readBody schema codecs maxRows rest
      else .error (.csv .headerMismatch)

end Silmaril.Formats.Csv.Typed.Utf8.Bounded
