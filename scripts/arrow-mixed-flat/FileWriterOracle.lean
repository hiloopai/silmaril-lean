module

import Silmaril.Formats.Arrow.MixedFlat.FileWriter.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.FileWriter.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs

open Silmaril Silmaril.Formats.Arrow

namespace Silmaril.ArrowMixedFileOracle

open MixedFlat

private def batch (rows : Nat) (text : List (Option String))
    (ints : List (Option Int32)) (binary : List (Option KBytes)) : OrderedWriter.BatchInput :=
  ⟨rows, [.utf8View "t" true text, .int32 "i" false ints, .binary "b" true binary]⟩

private def empty : OrderedWriter.BatchInput := batch 0 [] [] []

private def plainBatch (rows : Nat) (plain view : List (Option String))
    (ints : List (Option Int32)) (other : List (Option String))
    (binary : List (Option KBytes)) : OrderedWriter.BatchInput :=
  ⟨rows, [.utf8 "u" true plain, .utf8View "v" true view, .int32 "i" false ints,
    .utf8 "q" false other, .binary "b" true binary]⟩

private def emptyPlain : OrderedWriter.BatchInput := plainBatch 0 [] [] [] [] []

private def cases : List (String × List MixedFlat.Field × List OrderedWriter.BatchInput) :=
  [("mixed", empty.fields, [
    batch 3 [some "雪雪雪雪雪", none, some ""] [some (-7), some 0, some 42]
      [some (.leaf 13 255), some .empty, none],
    empty,
    batch 2 [some "é", some "a"] [some (-2147483648), some 2147483647]
      [some (.leaf 2 65408), some (.leaf 12 1)]]),
   ("schema_only", empty.fields, []), ("empty", empty.fields, [empty]),
   ("zero_width", [], [⟨3, []⟩, ⟨0, []⟩]),
   ("plain_mixed", emptyPlain.fields, [
     plainBatch 3 [none, some "", some "é雪"] [some "雪雪雪雪雪", none, some ""]
       [some (-7), some 0, some 42] [some "", some "é", some ("a".push (Char.ofNat 0) ++ "b")]
       [some (.leaf 13 255), some .empty, none],
     emptyPlain,
     plainBatch 2 [some "🙂", some "é"] [some "", some "é"] [some 1, some 2]
       [some "雪", some ""] [none, some (.leaf 2 65408)]]),
   ("plain_schema_only", emptyPlain.fields, []), ("plain_empty", emptyPlain.fields, [emptyPlain])]

private def unpack (bytes : ByteArray) : KBytes :=
  Silmaril.Formats.Arrow.Writer.emitWords 1 (bytes.data.toList.map UInt8.toNat)

private inductive CellObservation where
  | primitive (value : Value)
  | binary (octets : List UInt8)
  | text (value : String)
  deriving DecidableEq

private def observeCell : MixedFlat.Events.Cell → CellObservation
  | .primitive value => .primitive value
  | .binaryView value => .binary value.toList
  | .utf8View value => .text value

private def check (name : String) (wire : KBytes) (fields : List MixedFlat.Field)
    (expected : List OrderedWriter.BatchInput) : IO Unit := do
  let limits : MixedFlat.Limits := {}
  let .ok index := MixedFlat.File.readIndex limits.observation.ipc wire |
    throw (IO.userError s!"{name}: strict file index rejected")
  unless index.footer.fields == fields && index.footer.blocks.length == expected.length do
    throw (IO.userError s!"{name}: incorrect ordered schema or block count")
  let mut expectedColumns : List (List (List (Option CellObservation))) := []
  let mut nextOffset := 16 + index.schemaSize
  for ((block, input), n) in (index.footer.blocks.zip expected).zipIdx do
    let .ok (.metadata size) := readEnvelope limits.observation.ipc wire block.offset |
      throw (IO.userError s!"{name}: missing record envelope")
    let .ok metadata := MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers
        limits.totalDataBuffers fields (MixedFlat.File.metadataSlice wire block) |
      throw (IO.userError s!"{name}: record metadata rejected")
    unless block.offset == nextOffset && block.metadataLength == 8 + size &&
        block.bodyLength == metadata.bodyLength do
      throw (IO.userError s!"{name}: incorrect original block offsets or extents")
    let .ok (some observed) := index.readAt limits n |
      throw (IO.userError s!"{name}: indexed record rejected")
    unless MixedFlat.FileWriter.observe observed == input.observe do
      throw (IO.userError s!"{name}: wrong record order, row count or nullable values")
    expectedColumns := (observed.columns.map fun (_, column) =>
      (MixedFlat.Events.cells column).map (Option.map observeCell)) :: expectedColumns
    nextOffset := block.endOffset
  let .ok .eos := readEnvelope limits.observation.ipc wire nextOffset |
    throw (IO.userError s!"{name}: missing exact EOS")
  unless nextOffset + 8 == index.span.start do
    throw (IO.userError s!"{name}: unexpected gap before footer")
  let .ok none := index.readAt limits expected.length |
    throw (IO.userError s!"{name}: indexed end is not absent")
  let .ok ⟨signature, trace⟩ := MixedFlat.File.Events.Pull.readAll limits wire |
    throw (IO.userError s!"{name}: pull open failed")
  let .eos := trace.termination | throw (IO.userError s!"{name}: pull did not reach EOS")
  let columns := trace.batches.map fun event =>
    List.ofFn fun i : Fin signature.width => (event.values i).map (Option.map observeCell)
  unless List.ofFn (fun i : Fin signature.width => (signature.kind i).1) == fields &&
      trace.batches.map (·.rowCount) == expected.map (·.rowCount) && columns == expectedColumns.reverse do
    throw (IO.userError s!"{name}: wrong pull schema, row-count sequence or positional values")

public def run (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a fixture directory")
  let dir := System.FilePath.mk path
  for (name, fields, batches) in cases do
    let reference ← IO.FS.readBinFile (dir / s!"pyarrow-{name}.arrow")
    check s!"PyArrow {name}" (unpack reference) fields batches
    let .ok wire := MixedFlat.FileWriter.emit {} fields batches |
      throw (IO.userError s!"{name}: mixed file writer rejected input")
    check s!"Lean {name}" wire fields batches
    IO.FS.writeBinFile (dir / s!"lean-{name}.arrow") wire.toByteArray

end Silmaril.ArrowMixedFileOracle

public def main : List String → IO Unit := Silmaril.ArrowMixedFileOracle.run
