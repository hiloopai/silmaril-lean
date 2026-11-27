module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Defs

/-! Opt-in named import with a row budget enforced during typed CSV decoding. -/

@[expose] public section

namespace Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded

open Silmaril.Relational Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Kind Value)

inductive ReadError where
  | byteLimit (maximum actual : Nat)
  | decode (reason : Csv.Typed.Utf8.Bounded.Error)
  deriving DecidableEq

/-- Check the supplied wire byte cap before decoding. The row budget stops
before parsing a further body record and charges width-zero markers as rows. -/
def readCsv (limits : Limits) (declared : Scan.Schema String Kind) (wire : Csv.Bytes) :
    Except ReadError (Scan.Table declared Value) :=
  if wire.length > limits.maxBytes then .error (.byteLimit limits.maxBytes wire.length)
  else (Csv.Typed.Utf8.Bounded.decode limits.maxRows (ToCsv.csvSchema declared) ToCsv.codecs wire).mapError .decode

/-- Reject occupied names before reading. Install the complete typed table
only after EOS and exact agreement with the expected ordered schema. -/
def importCsv {Name : Type*} [DecidableEq Name] (db : Database Name) (name : Name)
    (expected declared : Scan.Schema String Kind) (limits : Limits) (wire : Csv.Bytes) :
    Except (NamedTable.ImportError ReadError) (Database Name) :=
  if (db name).isSome then .error .nameConflict
  else NamedTable.importCollected db name expected
    ((readCsv limits declared wire).map fun rows => ⟨⟨declared, rows⟩, .eos⟩)

end Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Bounded
