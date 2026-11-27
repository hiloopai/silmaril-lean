module

import Lean
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Defs
import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs

open Lean Silmaril.Formats.Compression Silmaril.Formats.Compression.Brotli

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def runJson (run : BlockTypes.Switch.Run) : Json := toJson [run.current, run.previous, run.remaining]

private def snapshot (bytes : List UInt8) (headerBit payloadBit : Nat) (state : Execute.InsertCopy.State)
    (reader : LSBReader) : Json :=
  let ring := state.execution.ring
  Json.mkObj [("bytes", toJson (bytes.map UInt8.toNat)), ("header", toJson headerBit),
    ("payload", toJson payloadBit), ("end", toJson reader.totalRead),
    ("ring", toJson [ring.latest, ring.second, ring.third, ring.fourth]),
    ("distanceRun", runJson state.runs.distance)]

private def failureJson (block : Nat) (failure : Execute.DistanceSwitch.BlockError) : Json :=
  let (command, stage, cause) : Option Nat × String × Json :=
    match failure with
    | .initialOutput _ => (none, "initialOutput", .null)
    | .fuel index _ => (some index, "fuel", .null)
    | .command index reason =>
      let (stage, cause) := match reason with
        | .distanceSwitch error => match error.cause with
          | .typeSymbol reason => ("switch-type", toJson (reprStr reason))
          | .length reason => ("switch-length", toJson (reprStr reason))
          | reason => ("switch", toJson (reprStr reason))
        | .distance _ reason => ("distance", toJson (reprStr reason))
        | .copy _ (.unsupportedDictionary distance size word) => ("dictionary", toJson [distance, size, word])
        | .copy _ reason => ("copy", toJson (reprStr reason))
        | .literal reason => ("literal", toJson (reprStr reason))
        | .commandPrefix reason => ("prefix", toJson (reprStr reason))
      (some index, stage, cause)
  Json.mkObj [("block", toJson block), ("command", toJson command), ("stage", toJson stage),
    ("bit", toJson failure.bit), ("cause", cause)]

public def main (args : List String) : IO UInt32 := do
  let [path, outputCap, bitCap] := args | return 2
  let some outputCap := outputCap.toNat? | return 2
  let some bitCap := bitCap.toNat? | return 2
  let wire ← IO.FS.readBinFile path
  let extent := wire.size * 8
  let (window, afterWindow) ← requireIO (Brotli.Internal.readWindow (Brotli.Internal.start wire.data.toList))
  let mut state := Execute.State.start
  let mut cursor := afterWindow
  let mut observations := #[]
  for index in [:wire.size] do
    let (framing, tables) ← requireIO (Stream.Internal.readHeader cursor)
    let .compressed last length := framing | throw (IO.userError "expected compressed fixture meta-block")
    let (header, payload) ← requireIO (CompressedHeader.read ⟨17408, 768, extent - tables.totalRead⟩ tables)
    let limits : Execute.Limits := ⟨outputCap, bitCap - payload.totalRead⟩
    match Execute.DistanceSwitch.readBlock header window length.size limits state payload with
    | .error error =>
      IO.println (Json.mkObj [("failure", failureJson index error)]).compress
      return 0
    | .ok (next, after) =>
      let chunk := next.execution.output.toList.drop state.output.size
      observations := observations.push (snapshot chunk tables.totalRead payload.totalRead next after)
      state := next.execution
      cursor := after
      if last then
        let limits : Stream.Limits := ⟨wire.size, outputCap, windowSize 24, bitCap, wire.size, 17408, 768⟩
        let finish := match Stream.Internal.finish limits cursor with
          | .ok _ => "ok"
          | .error (.framing .trailingInput) => "trailingInput"
          | .error error => reprStr error
        IO.println (Json.mkObj [("blocks", toJson observations), ("finish", toJson finish)]).compress
        return 0
  throw (IO.userError "missing final compressed block")
