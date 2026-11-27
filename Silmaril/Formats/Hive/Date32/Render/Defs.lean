module

public import Silmaril.Formats.Hive.Date32.Defs
public import Silmaril.Formats.Utf8.Defs

/-! # Canonical Hive URI directories for nullable DATE partition values -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32

open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)

inductive RenderError where
  | outsideDateProfile (day : DateInterop.Date32.Payload)
  | path (reason : PartitionPath.Error)
  deriving BEq, Repr

/-- The shared Gregorian printer emits ASCII for every admitted signed day. -/
def encodeText (day : DateInterop.Date32.Payload) : Except RenderError String :=
  match Csv.Typed.Codecs.Date32.print day with
  | some bytes => .ok (String.ofList (Utf8.ofAscii bytes))
  | none => .error (.outsideDateProfile day)

/-- A present-cell encoder for the existing Hive write plan. -/
def encode : WritePlan.Encode Cell RenderError := fun _ => encodeText

/-- Render one directory segment with the Hive URI policy. The marker is
compared against the canonical present text before percent escaping. -/
def renderDirectory (key : String) (options : PartitionPath.Options)
    (day : Option DateInterop.Date32.Payload) : Except RenderError String := do
  let text ← day.mapM encodeText
  (PartitionPath.render options [(key, text)]).mapError .path

end Silmaril.Formats.Hive.Date32
