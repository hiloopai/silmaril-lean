module

public import Silmaril.Formats.Hive.Date32.Utf8.Defs
public import Silmaril.Formats.Hive.Date32.Render.Defs

/-! # Canonical URI directories for paired DATE and UTF-8 virtual cells -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32.Utf8

open Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.File (Value)

inductive EncodeError where
  | date (cause : Date32.RenderError)
  | invalidUtf8
  deriving BEq, Repr

/-- Use the canonical DATE spelling and require valid UTF-8 for present text.
Virtual nulls bypass the encoder in the shared write plan. -/
def encode : WritePlan.Encode Value EncodeError := fun field =>
  match field.kind with
  | .int32 _ => fun day => (Date32.encodeText day).mapError .date
  | .byteArray _ => fun bytes =>
    match String.fromUTF8? bytes.data with
    | none => .error .invalidUtf8
    | some text => .ok text

/-- Encode the two declared cells, then use the URI renderer to check keys
and the decoded marker before assembling the directory. -/
def renderDirectory {keys : Keys} (options : PartitionPath.Options)
    (cells : Scan.Row keys.schema.toScan Value) : Except (WritePlan.RowError EncodeError) String := do
  let entries ← WritePlan.encodeEntries encode cells
  (PartitionPath.render options entries).mapError .render

end Silmaril.Formats.Hive.Date32.Utf8
