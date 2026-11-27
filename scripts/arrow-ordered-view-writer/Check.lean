module

import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
import Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews.Defs

open Silmaril Silmaril.Formats.Arrow.MixedFlat

private def bytes (octets : List Nat) : KBytes :=
  Silmaril.Formats.Arrow.Writer.emitWords 1 octets

private def longBytes (suffix : List Nat) : KBytes :=
  bytes ([255, 0, 254] ++ suffix)

private def rows (count : Nat) (text : List (Option String)) (blob : List (Option KBytes))
    (ints : List (Option Int32)) (notes : List (Option String)) (raw : List (Option KBytes)) :
    OrderedWriter.BatchInput :=
  ⟨count, [.utf8View "text" true text, .binary "blob" true blob, .int32 "ordinal" false ints,
    .utf8View "notes" false notes, .binary "raw" true raw]⟩

private def batches : List OrderedWriter.BatchInput :=
  [rows 4
    [none, some "", some "éééééé", some ("a".push (Char.ofNat 0) ++ "b")]
    [some (bytes [255, 0]), some (longBytes (List.range 12)), none, some KBytes.empty]
    [some (-7), some 0, some 42, some 2147483647]
    [some "ééééééé", some "雪🙂é", some "", some "é"]
    [some (bytes [195, 169]), none, some KBytes.empty, some (bytes [128])],
  rows 0 [] [] [] [] [],
  rows 3
    [some "雪雪雪雪雪", some "é", some "é"]
    [some KBytes.empty, some (bytes [255, 195]), none]
    [some (-2147483648), some 2, some 3]
    [some "🙂🙂🙂", some "雪", some ""]
    [some (longBytes (List.replicate 13 191)), none, some (bytes [0])]]

private def verify (wire : KBytes) (fields : List Field) (limits : Limits) (generated : Bool) : IO Unit := do
  let .ok decoded := Stream.read limits wire | throw (IO.userError "mixed IPC stream rejected")
  unless decoded.fields == fields && decoded.batches.map StreamWriter.observeBatch == batches.map (·.observe) do
    throw (IO.userError "wrong ordered labels, text, octets, or record boundaries")
  if generated then
    let assignments ← decoded.batches.mapM fun record => do
      let .ok metadata := readMetadata limits.observation.ipc limits.view.dataBuffers
          limits.totalDataBuffers fields (record.range.metadataSlice wire) |
        throw (IO.userError "mixed view metadata rejected")
      let .ok plan := bindBatch limits fields metadata (record.range.bodySlice wire) |
        throw (IO.userError "mixed view buffer binding rejected")
      return (metadata.counts, plan.assignment.groups.map (·.buffers.length))
    unless assignments == [
        ([0, 1, 1, 0], [2, 3, 2, 3, 2]), ([0, 0, 0, 0], [2, 2, 2, 2, 2]),
        ([1, 0, 0, 1], [3, 2, 2, 2, 3])] do
      throw (IO.userError "wrong text/binary count order or descriptor widths")

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a fixture directory")
  let directory := System.FilePath.mk path
  let limits : Limits := {}
  let fields := (rows 0 [] [] [] [] []).fields
  let .ok wire := OrderedWriter.emit limits fields batches |
    throw (IO.userError "ordered writer rejected explicitly typed mixed views")
  verify wire fields limits true
  let reference ← IO.FS.readBinFile (directory / "pyarrow.arrows")
  verify (bytes (reference.data.toList.map UInt8.toNat)) fields limits false

  let binary := OrderedWriter.Column.binary "value" true [some (bytes [195, 169])]
  let text := OrderedWriter.Column.utf8View "value" true [some "é"]
  let .error (.record 0 .schemaMismatch) := OrderedWriter.emit limits [text.field] [⟨1, [binary]⟩] |
    throw (IO.userError "valid UTF-8 bytes must retain their explicit BinaryView type")
  let .error (.record 0 .schemaMismatch) := OrderedWriter.emit limits [binary.field] [⟨1, [text]⟩] |
    throw (IO.userError "explicit Utf8View text must retain its field type")
  let capped : Limits := { view := { valueBytes := 3 } }
  let tooWide := OrderedWriter.Column.utf8View "value" true [some "éé"]
  let .error (.record 0 (.field 0 (.view 0 .valueLimit))) :=
    OrderedWriter.emit capped [tooWide.field] [⟨1, [tooWide]⟩] |
    throw (IO.userError "Utf8View value cap must count encoded bytes")
  let .error (.record 0 (.metadata .totalDataBufferLimit)) :=
    OrderedWriter.emit { totalDataBuffers := 1 } fields batches |
    throw (IO.userError "mixed text and binary views must share the aggregate buffer cap")
  let .error .unsupportedSchema := TwoBinaryViews.emit limits [binary.field, binary.field, text.field] [] |
    throw (IO.userError "the two-BinaryView profile must reject Utf8View")

  IO.FS.writeBinFile (directory / "lean.arrows") wire.toByteArray
  IO.println "Lean: exact text and octets, explicit count vectors, empty batch, and typed limits passed"
