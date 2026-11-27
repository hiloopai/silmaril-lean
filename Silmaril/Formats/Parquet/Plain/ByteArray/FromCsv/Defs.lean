module

public import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Defs
public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Defs

/-! Checked typed opaque CSV to one native unannotated PLAIN V1 BYTE_ARRAY leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv

open Csv.Typed.Utf8

inductive Error where
  | expectedBinaryView (actual : OpaqueIpc.Layout)
  | csv (cause : OpaqueIpc.CsvError)
  | requiredSlot
  | writer (cause : PlainByteArrayV1Writer.File.Error)
  deriving DecidableEq, Repr

def layout (nullable : Bool) : FlatColumn.Layout :=
  if nullable then .optional else .required

def prepare (field : OpaqueIpc.Descriptor) (values : OpaqueIpc.Slots) :
    Option PlainByteArrayV1Writer.File.Input :=
  let slots := values.map (Option.map Bytes.ofList)
  if field.nullable then some ⟨field.name, .optional slots⟩
  else (slots.mapM id).map fun present => ⟨field.name, .required present⟩

/-- Check the out-of-band BinaryView descriptor and the complete typed CSV
before offering one group of original nullable octets to the file writer.
Header-only CSV still writes one framed zero-row group. -/
def convert (csv : OpaqueIpc.CsvLimits) (limits : PlainByteArrayV1Writer.File.Limits)
    (field : OpaqueIpc.Descriptor) (input : Csv.Bytes) :
    Except Error PlainByteArrayV1Writer.File.Encoded := do
  if field.layout ≠ .binaryView then throw (.expectedBinaryView field.layout)
  let values ← (OpaqueIpc.decode csv field input).mapError .csv
  let some prepared := prepare field values | throw .requiredSlot
  (PlainByteArrayV1Writer.File.emit limits prepared).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.FromCsv
