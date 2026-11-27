module

import Lean
import Silmaril.Formats.Compression.Brotli.Stream.Defs
import Silmaril.Formats.Compression.Brotli.Execute.InsertCopy.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.Defs
meta import Silmaril.Formats.Compression.Brotli.Execute.InsertCopy.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def showError (error : Execute.InsertCopy.Error) : Json :=
  match error with
  | .switch failure =>
    let (stage, reason) :=
      match failure.cause with
      | .typeSymbol reason => ("type", reprStr reason)
      | .length reason => ("length", reprStr reason)
      | reason => ("run", reprStr reason)
    Json.mkObj [
      ("stage", toJson stage), ("bit", toJson failure.bit),
      ("category", toJson (reprStr failure.category)), ("cause", toJson reason)]
  | .execute bit reason =>
    Json.mkObj [("stage", toJson "execute"), ("bit", toJson bit), ("cause", toJson (reprStr reason))]
  | reason => Json.mkObj [("cause", toJson (reprStr reason))]

private def report (rows : Array (List Nat)) (output : Array UInt8)
    (endBit : Option Nat) (failure : Option Json) : IO UInt32 := do
  IO.println (Json.mkObj [
    ("output", toJson (output.toList.map UInt8.toNat)), ("commands", toJson rows),
    ("end", toJson endBit), ("failure", failure.getD Json.null)]).compress
  return 0

public def main (args : List String) : IO UInt32 := do
  let [path, maxOutput, maxBits] := args | return 2
  let some maxOutput := maxOutput.toNat? | return 2
  let some maxBits := maxBits.toNat? | return 2
  let wire ← IO.FS.readBinFile path
  let (window, afterWindow) ← requireIO (Brotli.Internal.readWindow (LSBReader.ofByteArray wire))
  let (envelope, afterEnvelope) ← requireIO (Stream.Internal.readHeader afterWindow)
  let .compressed true length := envelope | throw (IO.userError "expected one last compressed meta-block")
  let (header, payload) ← requireIO
    (CompressedHeader.read ⟨17408, 768, maxBits - afterEnvelope.totalRead⟩ afterEnvelope)
  let descriptor : Execute.Block := ⟨window, 0, length.size⟩
  let mut state := Execute.InsertCopy.State.start header Execute.State.start
  let mut cursor := payload
  let mut rows : Array (List Nat) := #[]
  for _ in [:length.size] do
    if state.execution.output.size == descriptor.endOutput then break
    match Execute.InsertCopy.read header descriptor ⟨maxOutput, maxBits - cursor.totalRead⟩ state cursor with
    | .error reason => return ← report rows state.execution.output none (some (showError reason))
    | .ok (result, after) =>
      let run := result.runs.insertCopy
      rows := rows.push [cursor.totalRead, after.totalRead, run.current, run.previous, run.remaining,
        result.execution.command.symbol.val, result.execution.state.output.size]
      state := result.state
      cursor := after
  unless state.execution.output.size == descriptor.endOutput do throw (IO.userError "unexpected command fuel")
  let limits : Stream.Limits := ⟨wire.size, maxOutput, windowSize 24, maxBits, 1, 17408, 768⟩
  let _ ← requireIO (Stream.Internal.finish limits cursor)
  report rows state.execution.output (some cursor.totalRead) none
