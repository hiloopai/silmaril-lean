module

import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Defs
meta import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Csv.Typed.Utf8
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

private def fields (table : Rows.Table) : List Arrow.MixedFlat.Field :=
  List.ofFn fun i => (table.schema.kind i).1

private def cells (table : Rows.Table) : List (List (Option Cell)) :=
  table.rows.map fun row => List.ofFn row

private def expectError {α ε : Type} [DecidableEq ε] [Repr ε] (label : String)
    (result : Except ε α) (expected : ε) : IO Unit := do
  let .error actual := result | throw (IO.userError s!"{label}: unexpected output")
  unless actual == expected do
    throw (IO.userError s!"{label}: got {repr actual}, expected {repr expected}")

public def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk root
  let bytes ← IO.FS.readBinFile (directory / "producer" / "mixed.arrows")
  let input := KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

  let source : Arrow.MixedFlat.Limits := { observation := {
    ipc := { fields := 4, rows := 2, batches := 3 }, totalRows := 4, totalCells := 16 } }
  let sink : Arrow.MixedFlat.Limits := { observation := {
    ipc := { fields := 4, rows := 4, batches := 1 }, totalRows := 4, totalCells := 16 } }
  let exportLimits : MixedIpc.Limits := { maxBytes := 2048, maxRows := 5 }
  let .ok exported := MixedIpc.convert source exportLimits input
    | throw (IO.userError "native IPC to typed CSV failed")
  let importLimits : MixedIpc.Limits := ⟨exported.wire.length, 4⟩
  let .ok output := MixedIpc.ToIpc.convert importLimits sink exported.schema exported.wire
    | throw (IO.userError "typed CSV to native IPC failed")

  let some original := Rows.readRows source input | throw (IO.userError "input Scan failed")
  let some returned := Rows.readRows sink output | throw (IO.userError "output Scan failed")
  let some before := readEvents source input | throw (IO.userError "input event exhaustion failed")
  let some after := readEvents sink output | throw (IO.userError "output event exhaustion failed")
  unless fields original == fields returned && cells original == cells returned &&
      before.fields == after.fields && before.batches.map Prod.fst == [2, 0, 2] &&
      after.batches.map Prod.fst == [4] do
    throw (IO.userError "the round trip changed Scan rows, descriptors, or the single-batch policy")

  let limitedSource : Arrow.MixedFlat.Limits :=
    { source with observation := { source.observation with
        ipc := { source.observation.ipc with batches := 2 } } }
  match MixedIpc.convert limitedSource exportLimits input with
  | .error (.input (.ipc (.message 2 _ .batchLimit))) => pure ()
  | .error cause => throw (IO.userError s!"wrong late source refusal: {repr cause}")
  | .ok _ => throw (IO.userError "late source limit yielded CSV")
  expectError "CSV re-import row cap"
    (MixedIpc.ToIpc.convert { importLimits with maxRows := 3 } sink exported.schema exported.wire)
    (.source (.rowLimit 3))
  let limitedSink : Arrow.MixedFlat.Limits :=
    { sink with observation := { sink.observation with ipc := { sink.observation.ipc with batches := 0 } } }
  expectError "writer batch cap" (MixedIpc.ToIpc.convert importLimits limitedSink exported.schema exported.wire)
    (.writer (.ipc (.limit .batches)))

  IO.FS.writeBinFile (directory / "roundtrip.csv") ⟨exported.wire.toArray⟩
  IO.FS.writeBinFile (directory / "roundtrip.arrows") output.toByteArray
  IO.println "Exact Scan rows agree under independent limits, with batches [2, 0, 2] to [4] and three typed refusals."
