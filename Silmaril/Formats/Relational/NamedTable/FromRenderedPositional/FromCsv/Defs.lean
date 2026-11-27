module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv.Defs

/-! Checked import of the exact rendered positional typed CSV profile. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv

open Silmaril.Relational Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Kind Value)

structure Limits where
  maxBytes : Nat
  maxRows : Nat

inductive ReadError where
  | byteLimit (maximum actual : Nat)
  | rowLimit (maximum actual : Nat)
  | csv (reason : Csv.Typed.Error)
  deriving DecidableEq

/-- Check wire size before decoding, then check the admitted data-row count
after decoding. The row cap also applies to the zero-column marker rows. -/
def readCsv (limits : Limits) (declared : Scan.Schema String Kind) (wire : Csv.Bytes) :
    Except ReadError (Scan.Table declared Value) :=
  if wire.length > limits.maxBytes then .error (.byteLimit limits.maxBytes wire.length)
  else
    match Csv.Typed.Utf8.decode (ToCsv.csvSchema declared) ToCsv.codecs wire with
    | .error reason => .error (.csv reason)
    | .ok rows =>
      if rows.length > limits.maxRows then .error (.rowLimit limits.maxRows rows.length)
      else .ok rows

/-- The declared schema determines the ordered header and cell codecs.
Only a vacant destination with the exact expected String/Kind schema
receives the complete decoded table. -/
def importCsv {Name : Type*} [DecidableEq Name] (db : Database Name) (name : Name)
    (expected declared : Scan.Schema String Kind) (limits : Limits) (wire : Csv.Bytes) :
    Except (NamedTable.ImportError ReadError) (Database Name) :=
  if (db name).isSome then .error .nameConflict
  else NamedTable.importCollected db name expected
    ((readCsv limits declared wire).map fun rows => ⟨⟨declared, rows⟩, .eos⟩)

end Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv
