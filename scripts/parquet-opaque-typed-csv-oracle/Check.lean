module

import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv
open Silmaril.Formats.Csv.Typed.Utf8

private def expectError {α : Type} (label : String) (result : Except ToCsv.Error α)
    (expected : ToCsv.Error) : IO Unit := do
  let .error actual := result | throw (IO.userError s!"{label}: unexpected result")
  unless actual == expected do
    throw (IO.userError s!"{label}: got {repr actual}, expected {repr expected}")

private def loadIpc (path : System.FilePath) : IO KBytes := do
  let raw ← IO.FS.readBinFile path
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def checkFailures (root : System.FilePath) (input : Bytes) (output : ToCsv.Output) : IO Unit := do
  let badIpc : OpaqueIpc.IpcLimits := { ipc := { batches := 0 } }
  let badCsv : OpaqueIpc.CsvLimits := { maxRows := 0, maxBytes := 0 }
  expectError "missing projection"
    (convert {} badIpc badIpc badCsv badCsv input "other" .optional)
    (.parquetToIpc (.source (.openError (.schema (.unknownLeaf "other")))))
  let .error (.parquetToIpc (.source (.openError (.schema (.leafMismatch 1 _))))) :=
      convert {} badIpc badIpc badCsv badCsv input "blob" .required
    | throw (IO.userError "selected nullability mismatch did not win")

  let late : Bytes := ⟨← IO.FS.readBinFile (root / "source" / "late-length-error.parquet")⟩
  let cause := FlatColumn.Error.page 1 1 "blob" 0 136 (.decode (.scalar (.plain .integerOverflow)))
  expectError "late source error before both writers and both CSV caps"
    (convert {} badIpc badIpc badCsv badCsv late "blob" .optional)
    (.parquetToIpc (.source (.readError cause)))
  let .ok ⟨_, trace⟩ := File.readAll {} late "blob" .optional
    | throw (IO.userError "late source failure lost its opened trace")
  unless trace.batches.map (·.rowCount) == [4] && trace.termination == .readError (.column cause) do
    throw (IO.userError "late source failure changed its completed prefix")
  expectError "intermediate writer cap"
    (convert {} { ipc := { batches := 1 } } badIpc badCsv badCsv input "blob" .optional)
    (.parquetToIpc (.writer (.ipc (.limit .batches))))
  expectError "intermediate writer indexed value cap"
    (convert {} { view := { valueBytes := 12 } } badIpc badCsv badCsv input "blob" .optional)
    (.parquetToIpc (.writer (.record 1 (.column .valueLimit))))
  expectError "CSV export row cap"
    (convert {} {} badIpc { maxRows := 7 } badCsv input "blob" .optional)
    (.toCsv (.csv (.rowLimit 7)))
  let size := output.csv.wire.length
  expectError "CSV export byte cap"
    (convert {} {} badIpc { maxBytes := size - 1 } badCsv input "blob" .optional)
    (.toCsv (.csv (.byteLimit (size - 1) size)))
  expectError "CSV import row cap before final writer"
    (convert {} {} badIpc {} { maxRows := 7 } input "blob" .optional)
    (.fromCsv (.csv (.rowLimit 7)))
  expectError "final writer batch cap"
    (convert {} {} badIpc {} {} input "blob" .optional)
    (.fromCsv (.writer (.view (.ipc (.limit .batches)))))
  expectError "final single-batch row cap"
    (convert {} { ipc := { rows := 4 } } { ipc := { rows := 4 } } {} {} input "blob" .optional)
    (.fromCsv (.writer (.view (.record 0 (.ipc (.limit .rows))))))

private def check (root : System.FilePath) (file stem name : String)
    (layout : FlatColumn.Layout) (counts : List Nat) : IO Unit := do
  let input : Bytes := ⟨← IO.FS.readBinFile (root / "source" / file)⟩
  let wire ← loadIpc (root / "source" / (stem ++ ".arrows"))
  let field := descriptor name layout
  let source : OpaqueIpc.IpcLimits := {
    ipc := { fields := 1, rows := counts.foldl max 0, batches := counts.length } }
  let sink : OpaqueIpc.IpcLimits := { ipc := { fields := 1, rows := counts.sum, batches := 1 } }
  let exportLimits : OpaqueIpc.CsvLimits := { maxRows := counts.sum }
  let .ok checked := ToIpc.readSource {} input name layout
    | throw (IO.userError s!"{stem}: checked source failed")
  let all := checked.groups.map (List.map (Option.map Bytes.toList))
  let .ok observed := OpaqueIpc.readIpc source .binaryView wire
    | throw (IO.userError s!"{stem}: intermediate IPC did not exhaust")
  unless observed == ⟨field, all⟩ && all.map List.length == counts do
    throw (IO.userError s!"{stem}: intermediate changed the original groups")
  let .ok staged := OpaqueIpc.toCsv source exportLimits .binaryView wire
    | throw (IO.userError s!"{stem}: intermediate wire to CSV failed")
  let limits : OpaqueIpc.CsvLimits := ⟨staged.wire.length, counts.sum⟩
  let .ok output := convert {} source sink exportLimits limits input name layout
    | throw (IO.userError s!"{stem}: conversion failed")
  let .ok actual := OpaqueIpc.readIpc sink .binaryView output.ipc
    | throw (IO.userError s!"{stem}: final IPC did not exhaust")
  let .ok slots := OpaqueIpc.decode limits output.csv.field output.csv.wire
    | throw (IO.userError s!"{stem}: CSV decode failed")
  let independent ← IO.FS.readBinFile (root / "source" / (stem ++ ".csv"))
  let .ok independentWire := OpaqueIpc.fromCsv ⟨independent.size, counts.sum⟩ sink field independent.data.toList
    | throw (IO.userError s!"{stem}: independent CPython CSV refused")
  unless output.csv == staged && slots == all.flatten && actual == ⟨field, [all.flatten]⟩ &&
      output.ipc.toList == independentWire.toList do
    throw (IO.userError s!"{stem}: changed descriptor, flattened rows or independent CSV result")
  if stem == "optional-v2" then checkFailures root input output
  IO.FS.writeBinFile (root / (stem ++ ".csv")) ⟨output.csv.wire.toArray⟩
  IO.FS.writeBinFile (root / (stem ++ ".arrows")) output.ipc.toByteArray

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected fixture directory")
  let root := System.FilePath.mk directory
  check root "selected.parquet" "optional-v2" "blob" .optional [4, 4]
  check root "plain-byte-array-v1.parquet" "required-v1" "key" .required [12, 12, 12]
  check root "schema-only.parquet" "schema-only" "blob" .optional []
  check root "framed-zero-row-group.parquet" "empty-batch" "blob" .optional [0]
  IO.println "Four Parquet-to-CSV-to-IPC readbacks, four independent CSV inputs and ten typed refusal controls passed."
