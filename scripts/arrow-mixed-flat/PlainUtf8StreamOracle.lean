module

import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs

open Silmaril Silmaril.Formats.Arrow

namespace Silmaril.ArrowPlainUtf8StreamOracle

open MixedFlat

private def plainBatch (rows : Nat) (plain view : List (Option String))
    (ints : List (Option Int32)) (other : List (Option String))
    (binary : List (Option KBytes)) : OrderedWriter.BatchInput :=
  ⟨rows, [.utf8 "u" true plain, .utf8View "v" true view, .int32 "i" false ints,
    .utf8 "q" false other, .binary "b" true binary]⟩

private def emptyPlain : OrderedWriter.BatchInput := plainBatch 0 [] [] [] [] []

private def cases : List (String × List MixedFlat.Field × List OrderedWriter.BatchInput) :=
  [("plain_mixed", emptyPlain.fields, [
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
  let .ok decoded := MixedFlat.Stream.read limits wire |
    throw (IO.userError s!"{name}: eager stream read failed")
  unless decoded.fields == fields && decoded.batches.map MixedFlat.StreamWriter.observeBatch ==
      expected.map OrderedWriter.BatchInput.observe do
    throw (IO.userError s!"{name}: wrong field descriptors, nullable values or batch order")
  let .ok (.metadata schemaSize) := readEnvelope limits.observation.ipc wire 0 |
    throw (IO.userError s!"{name}: missing the first Schema")
  let mut next := 8 + schemaSize
  for record in decoded.batches do
    let range := record.range
    unless range.offset == next do throw (IO.userError s!"{name}: wrong record offset")
    next := range.next
  let .ok .eos := readEnvelope limits.observation.ipc wire next |
    throw (IO.userError s!"{name}: missing terminal EOS")
  unless next + 8 == wire.len do throw (IO.userError s!"{name}: trailing bytes after EOS")
  let .ok ⟨signature, trace⟩ := MixedFlat.Stream.Events.readAll limits wire |
    throw (IO.userError s!"{name}: pull open failed")
  let .eos := trace.termination | throw (IO.userError s!"{name}: pull did not reach EOS")
  let columns := trace.batches.map fun event =>
    List.ofFn fun i : Fin signature.width => (event.values i).map (Option.map observeCell)
  let expectedColumns := decoded.batches.map fun record => record.observed.columns.map fun (_, column) =>
    (MixedFlat.Events.cells column).map (Option.map observeCell)
  unless List.ofFn (fun i : Fin signature.width => (signature.kind i).1) == fields &&
      trace.batches.map (·.rowCount) == expected.map (·.rowCount) && columns == expectedColumns do
    throw (IO.userError s!"{name}: wrong pull schema, row counts or positional values")

public def run (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a fixture directory")
  let dir := System.FilePath.mk path
  for (name, fields, batches) in cases do
    let reference ← IO.FS.readBinFile (dir / s!"pyarrow-{name}.arrows")
    check s!"PyArrow {name}" (unpack reference) fields batches
    let .error .unsupportedSchema := OrderedWriter.emit {} fields batches |
      throw (IO.userError s!"{name}: default profile must reject plain Utf8")
    let .ok wire := OrderedWriter.emitWith {} fields batches (fun signature => signature == fields) |
      throw (IO.userError s!"{name}: explicit ordered profile rejected input")
    check s!"Lean {name}" wire fields batches
    IO.FS.writeBinFile (dir / s!"lean-{name}.arrows") wire.toByteArray

end Silmaril.ArrowPlainUtf8StreamOracle

public def main : List String → IO Unit := Silmaril.ArrowPlainUtf8StreamOracle.run
