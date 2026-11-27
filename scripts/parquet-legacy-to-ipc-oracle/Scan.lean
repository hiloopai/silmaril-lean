module

import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Defs
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan

private def project (positions : List Nat) : Projection := fun selected =>
  Scan.Projection.ofArray ((positions.filterMap fun i =>
    if h : i < selected.width then some ⟨i, h⟩ else none).toArray)

private def byOrdinal : Predicate := fun selected row => do
  let position ← if h : 0 < selected.width then some ⟨0, h⟩ else none
  match kind : (selected.kind position).2 with
  | .int32 _ =>
    let value : Int32 ← cast (congrArg (fun k => Option (Legacy.Value k)) kind) (row position)
    return value.toInt % 13 == 5 || value.toInt % 64 == 0 || value.toInt == 372
  | .byteArray _ => none

private def byPayload : Predicate := fun selected row => do
  let position ← if h : 1 < selected.width then some ⟨1, h⟩ else none
  match kind : (selected.kind position).2 with
  | .byteArray _ =>
    let value : Bytes ← cast (congrArg (fun k => Option (Legacy.Value k)) kind) (row position)
    return value.length > 8
  | .int32 _ => none

private def inlineOnly : Predicate := fun selected row => do
  let position ← if h : 1 < selected.width then some ⟨1, h⟩ else none
  match kind : (selected.kind position).2 with
  | .byteArray _ =>
    let value : Bytes ← cast (congrArg (fun k => Option (Legacy.Value k)) kind) (row position)
    return value.length ≤ 12
  | .int32 _ => none

private def discard : Predicate := fun _ _ => some false

private def load (directory : System.FilePath) (name : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (name ++ ".parquet"))⟩

private def convertNamed (input : Bytes) (positions : List Nat) (keep : Predicate)
    (ipc : Arrow.MixedFlat.Limits := {}) : Except Legacy.ToIpc.Scan.Error KBytes :=
  convert {} ipc input "ordinal" "payload" (project positions) keep

private def verifyLayout (wire : KBytes) (fields : List Arrow.MixedFlat.Field)
    (rows : List Nat) (layouts : List (List (Option Nat) × List Nat)) : IO Unit := do
  let limits : Arrow.MixedFlat.Limits := {}
  let .ok observed := Stream.read limits wire | throw (IO.userError "rejected ordered stream")
  unless observed.batches.map (·.observed.rowCount) == rows do
    throw (IO.userError "wrong independent view rows")
  let actual ← observed.batches.mapM fun record => do
    let .ok metadata := Arrow.MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers
        limits.totalDataBuffers fields (record.range.metadataSlice wire) |
      throw (IO.userError "rejected independent count vector")
    let .ok plan := Arrow.MixedFlat.bindBatch limits fields metadata (record.range.bodySlice wire) |
      throw (IO.userError "rejected independent descriptor ranges")
    return (plan.assignment.groups.map Group.count, plan.assignment.groups.map (·.buffers.length))
  unless actual == layouts do
    throw (IO.userError "wrong independent count ordinals or descriptor widths")

private def independentViews (directory : System.FilePath) : IO Unit := do
  let input ← load directory "opaque"
  let .ok checked := Legacy.openFile {} input "ordinal" "payload" |
    throw (IO.userError "could not bind the independent-view fixture")
  let .ok first := Legacy.readGroup checked 0 | throw (IO.userError "missing first opaque group")
  let .ok last := Legacy.readGroup checked 2 | throw (IO.userError "missing last opaque group")
  let some short := first[0]?.bind Prod.snd | throw (IO.userError "missing short opaque slot")
  let some long := last[372]?.bind Prod.snd | throw (IO.userError "missing long opaque slot")
  let toWire := fun (bytes : Bytes) => Arrow.Writer.emitWords 1 (bytes.toList.map UInt8.toNat)
  let short := toWire short
  let long := toWire long
  let batch := fun (rows : Nat) left right =>
    (⟨rows, [.binary "left" true left, .binary "right" true right]⟩ : TwoBinaryViews.BatchInput)
  let batches := [batch 2 [some short, none] [some long, some long], batch 2 [some long, none]
    [some short, some KBytes.empty], batch 0 [] []]
  let fields := (batch 0 [] []).fields
  let limits : Arrow.MixedFlat.Limits := {}
  let .ok wire := TwoBinaryViews.emit limits fields batches |
    throw (IO.userError "standalone two-view writer rejected distinct inputs")
  verifyLayout wire fields [2, 2, 0]
    [([some 0, some 1], [2, 3]), ([some 1, some 0], [3, 2]), ([some 0, some 0], [2, 2])]
  IO.FS.writeBinFile (directory / "independent-views.arrows") wire.toByteArray

  let ordered := fun (rows : Nat) left middle right firstInts secondInts =>
    (⟨rows, [.binary "left" true left, .int32 "ordinal" false firstInts,
      .binary "middle" true middle, .int32 "ordinal" false secondInts,
      .binary "right" true right]⟩ : OrderedWriter.BatchInput)
  let empty := ordered 0 [] [] [] [] []
  let orderedBatches := [
    ordered 2 [some short, none] [some long, some long] [none, some KBytes.empty]
      [some 5, some 6] [some 8, some 9],
    ordered 2 [some long, none] [some short, some KBytes.empty] [some long, some short]
      [some (-10), some 12] [some 21, some (-13)],
    empty]
  let .error .unsupportedSchema := TwoBinaryViews.emit limits empty.fields orderedBatches |
    throw (IO.userError "the explicit two-view profile must reject a third view")
  let .ok orderedWire := OrderedWriter.emit limits empty.fields orderedBatches |
    throw (IO.userError "ordered writer rejected interleaved inputs")
  verifyLayout orderedWire empty.fields [2, 2, 0] [
    ([some 0, none, some 1, none, some 0], [2, 2, 3, 2, 2]),
    ([some 1, none, some 0, none, some 1], [3, 2, 2, 2, 3]),
    ([some 0, none, some 0, none, some 0], [2, 2, 2, 2, 2])]
  IO.FS.writeBinFile (directory / "ordered-independent.arrows") orderedWire.toByteArray

  let .ok zeroWire := OrderedWriter.emit limits [] [⟨2, []⟩, ⟨0, []⟩, ⟨1, []⟩] |
    throw (IO.userError "ordered writer rejected a zero-column schema")
  verifyLayout zeroWire [] [2, 0, 1] [([], []), ([], []), ([], [])]
  IO.FS.writeBinFile (directory / "ordered-zero-width.arrows") zeroWire.toByteArray

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the fixture directory")
  let directory := System.FilePath.mk path
  let cases := [
    ("payload-by-ordinal", [1], byOrdinal),
    ("ordinal-by-payload", [0], byPayload),
    ("reordered", [1, 0], byOrdinal),
    ("paired-by-payload", [0, 1], byPayload),
    ("repeated-int32", [0, 0], byPayload),
    ("zero-width", [], byPayload),
    ("discard-all", [1, 0], discard),
    ("two-views", [1, 1], byOrdinal),
    ("int-first", [0, 1, 1], byPayload),
    ("int-middle", [1, 0, 1], byOrdinal),
    ("int-last", [1, 1, 0], byPayload),
    ("two-views-discard-all", [1, 0, 1], discard),
    ("ordered-five", [1, 0, 1, 0, 1], byOrdinal),
    ("ordered-six", [0, 1, 1, 0, 1, 0], byPayload),
    ("ordered-inline-only", [1, 1, 0, 1, 0], inlineOnly),
    ("ordered-discard-all", [1, 0, 1, 0, 1], discard)]
  for name in ["original", "opaque"] do
    let input ← load directory name
    for (label, positions, keep) in cases do
      match convertNamed input positions keep with
      | .error cause => throw (IO.userError s!"{name} {label}: {repr cause}")
      | .ok wire => IO.FS.writeBinFile (directory / s!"{name}-{label}.arrows") wire.toByteArray
  let original ← load directory "original"
  let .error .unsupportedSchema :=
    OrderedWriter.emit {} [⟨"other", true, .primitive .utf8⟩] [] |
    throw (IO.userError "ordered writer must refuse classic Utf8")
  let fieldCap : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 4 } } }
  let .error (.budget (.limit .fields)) := convertNamed original [1, 0, 1, 0, 1] byOrdinal fieldCap |
    throw (IO.userError "projected field budget did not refuse a fifth field")
  let cellCap : Arrow.MixedFlat.Limits := { observation := { totalCells := 369 } }
  let .error (.budget (.limit .totalCells)) := convertNamed original [1, 0, 1, 0, 1] byOrdinal cellCap |
    throw (IO.userError "repeated fields must count toward the aggregate cell budget")
  let twoBuffers : Arrow.MixedFlat.Limits := { totalDataBuffers := 2 }
  let .error (.orderedWriter (.record 0 (.metadata .totalDataBufferLimit))) :=
    convertNamed original [1, 0, 1, 0, 1] byOrdinal twoBuffers |
    throw (IO.userError "all three view counts must contribute to the buffer cap")
  let singleDataBuffer : Arrow.MixedFlat.Limits := { totalDataBuffers := 1 }
  let .error (.twoViewWriter (.record 0 (.metadata .totalDataBufferLimit))) :=
    convertNamed original [1, 0, 1] byOrdinal singleDataBuffer |
    throw (IO.userError "both projected views must count their independent data buffer")
  let lowIpc : Arrow.MixedFlat.Limits := { observation := { totalRows := 0 } }
  let .error (.budget (.limit .totalRows)) := convertNamed original [] byPayload lowIpc |
    throw (IO.userError "zero-width rows must still count toward the IPC budget")
  let damaged ← load directory "damaged"
  for positions in [[], [1, 0], [1, 1], [1, 0, 1], [1, 0, 1, 0, 1]] do
    let .error (.source (.byteArray (.page 2 1 "payload" 19 21009
        (.decode (.plain (.plain .integerOverflow)))))) :=
      convertNamed damaged positions discard lowIpc |
      throw (IO.userError "late indexed failure must prevent a carrier before projection and writer refusal")
  let .error (.source (.byteArray (.page 2 1 "payload" 19 21009
      (.decode (.plain (.plain .integerOverflow)))))) :=
    convertNamed damaged [1, 0, 1, 0, 1] discard fieldCap |
    throw (IO.userError "late failure must take precedence over the projected field limit")
  independentViews directory
  IO.println "Lean: ordered projections, independent view ranges, zero-column counts, IPC caps and late source precedence passed"
