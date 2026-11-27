module

import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Defs
meta import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc

private def loadIpc (path : System.FilePath) : IO KBytes := do
  let raw ← IO.FS.readBinFile path
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def expectError {ε α : Type} [DecidableEq ε] [Repr ε] (label : String)
    (result : Except ε α) (expected : ε) : IO Unit := do
  let .error actual := result | throw (IO.userError s!"{label}: unexpected success")
  unless actual == expected do
    throw (IO.userError s!"{label}: got {repr actual}, expected {repr expected}")

private def checkLimits (input : KBytes) (source sink : IpcLimits) (csv : Output) (count : Nat) : IO Unit := do
  let trailing := input ++ Arrow.Writer.emitWords 1 [0]
  let limitedWriter := { sink with ipc := { sink.ipc with batches := 0 } }
  let (sourceError, writerError) : ToCsvError × FromCsvError :=
    match csv.field.layout with
    | .binaryView => (.source (.view (.batch 3 .trailingBytes)), .writer (.view (.ipc (.limit .batches))))
    | .binary => (.source (.binary (.record ⟨3, input.len - 8, .trailingBytes⟩)),
      .writer (.binary (.ipc (.limit .batches))))
  expectError "late carrier refusal before CSV limit"
    (toCsv source { maxRows := 0 } csv.field.layout trailing) sourceError
  expectError "aggregate CSV row cap"
    (toCsv source { maxRows := count - 1 } csv.field.layout input) (.csv (.rowLimit (count - 1)))
  expectError "writer cap"
    (fromCsv {} limitedWriter csv.field csv.wire) writerError

private def checkCsv : IO Unit := do
  let field : Descriptor := ⟨"payload", false, .binaryView⟩
  let run := fun text : String => fromCsv {} {} field text.toUTF8.data.toList
  for token in ["Ta0", "TA", "TAA BB", "T0xAA"] do
    expectError token (run s!"payload\r\n{token}\r\n") (.csv (.csv (.parseCell 0)))
  expectError "required null" (run "payload\r\nN\r\n") (.csv (.requiredNull 0))
  expectError "header mismatch" (run "other\r\nT00\r\n") (.csv (.csv .headerMismatch))
  expectError "no opaque octets directly in UTF-8 CSV" (fromCsv {} {} field [255]) (.csv (.csv .malformedWire))
  let wire := "payload\r\nT00\r\n".toUTF8.data.toList
  expectError "input byte cap" (fromCsv { maxBytes := wire.length - 1 } {} field wire)
    (.csv (.byteLimit (wire.length - 1) wire.length))

private def check (root : System.FilePath) (name : String) (field : Descriptor)
    (counts : List Nat) : IO Unit := do
  let input ← loadIpc (root / "producer" / (name ++ ".arrows"))
  let source : IpcLimits := { ipc := { fields := 1, rows := counts.foldl max 0, batches := counts.length } }
  let count := counts.sum
  let sink : IpcLimits := { ipc := { fields := 1, rows := count, batches := 1 } }
  let .ok original := readIpc source field.layout input
    | throw (IO.userError s!"{name}: source did not exhaust")
  let .ok csv := toCsv source { maxRows := count } field.layout input
    | throw (IO.userError s!"{name}: IPC to CSV failed")
  unless original.field == field && original.batches.map List.length == counts && csv.field == field do
    throw (IO.userError s!"{name}: source descriptor or batch counts changed")
  let .ok emitted := fromCsv ⟨csv.wire.length, count⟩ sink csv.field csv.wire
    | throw (IO.userError s!"{name}: Lean CSV import failed")
  let independent ← IO.FS.readBinFile (root / "producer" / (name ++ ".csv"))
  let .ok independentOutput := fromCsv ⟨independent.size, count⟩ sink field independent.data.toList
    | throw (IO.userError s!"{name}: CPython CSV import failed")
  let .ok reopened := readIpc sink field.layout emitted
    | throw (IO.userError s!"{name}: output did not exhaust")
  unless reopened == ⟨field, [original.batches.flatten]⟩ && emitted.toList == independentOutput.toList do
    throw (IO.userError s!"{name}: exact readback or independent input differs")
  if counts == [2, 0, 3] then checkLimits input source sink csv count
  IO.FS.writeBinFile (root / (name ++ ".csv")) ⟨csv.wire.toArray⟩
  IO.FS.writeBinFile (root / (name ++ ".arrows")) emitted.toByteArray

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected fixture directory")
  let root := System.FilePath.mk directory
  check root "view" ⟨"octets, café", true, .binaryView⟩ [2, 0, 3]
  check root "binary" ⟨"octets, café", true, .binary⟩ [2, 0, 3]
  check root "schema-only" ⟨"empty", true, .binaryView⟩ []
  check root "required" ⟨"required", false, .binary⟩ [2, 0]
  let text ← loadIpc (root / "producer" / "text.arrows")
  expectError "Utf8View descriptor" (toCsv {} {} .binaryView text) (.source (.unsupportedView "text" true))
  checkCsv
  IO.println "Four complete native round trips, four independent CSV inputs and fifteen typed refusals checked."
