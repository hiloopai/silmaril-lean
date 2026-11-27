module

import Lean
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Defs
import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs

open Lean Silmaril.Formats.Compression Silmaril.Formats.Compression.Brotli
open Execute.DistanceSwitch.Dictionary (read)

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error reason => throw (IO.userError (reprStr reason))
  | .ok value => pure value

private def commandJson (result : Execute.InsertCopy.Result) (after : LSBReader) : Json :=
  let cmd := result.execution.command
  let state := result.execution.state
  let ring := state.ring
  toJson ([
    toJson cmd.symbol.val, toJson cmd.insertLength, toJson cmd.copyLength, toJson result.execution.distance,
    toJson state.output.size, toJson after.totalRead, toJson [ring.latest, ring.second, ring.third, ring.fourth]
  ] : List Json)

private def errorJson (command : Nat) (reason : Execute.DistanceSwitch.Error) : Json :=
  let (stage, label) := match reason with
    | .copy _ .metaBlockExtent => ("copy", "metaBlockExtent")
    | .copy _ .outputLimit => ("copy", "outputLimit")
    | .distance _ .dictionaryWord => ("distance", "dictionaryWord")
    | .distance _ .dictionaryLength => ("distance", "dictionaryLength")
    | .distance _ .extraBitLimit => ("distance", "extraBitLimit")
    | _ => ("other", reprStr reason)
  Json.mkObj [("command", toJson command), ("bit", toJson reason.bit),
    ("stage", toJson stage), ("reason", toJson label)]

public def main (args : List String) : IO UInt32 := do
  let [path, outputArg, bitsArg] := args | return 2
  let (some output, some bitCap) := (outputArg.toNat?, bitsArg.toNat?) | return 2
  let bytes ← IO.FS.readBinFile path
  let extent := bytes.size * 8
  let wire := bytes.data.toList
  let (window, afterWindow) ← requireIO (Brotli.Internal.readWindow (Brotli.Internal.start wire))
  let (frame, atHeader) ← requireIO (Stream.Internal.readHeader afterWindow)
  let .compressed true length := frame | throw (IO.userError "expected one final compressed meta-block")
  let (header, payload) ← requireIO (CompressedHeader.read ⟨17408, 768, extent - atHeader.totalRead⟩ atHeader)
  let block : Execute.Block := ⟨window, 0, length.size⟩
  let mut cursor := payload
  let mut state := Execute.InsertCopy.State.start header Execute.State.start
  let mut observations := #[]
  -- Test-driver fuel is independent of the native trace.
  for index in [:extent + length.size] do
    match read header block ⟨output, bitCap - cursor.totalRead⟩ state cursor with
    | .error error =>
      IO.println (Json.mkObj [("failure", errorJson index error)]).compress
      return 0
    | .ok (next, after) =>
      observations := observations.push (commandJson next after)
      state := next.state
      cursor := after
      if state.execution.output.size = block.endOutput then
        let limits : Stream.Limits := ⟨bytes.size, output, windowSize 24, bitCap, 1, 17408, 768⟩
        let _ ← requireIO (Stream.Internal.finish limits cursor)
        let old := Stream.DistanceSwitch.decode limits wire
        let refuses := match old with
          | .error (.block _ (.command _ (.copy _ (.unsupportedDictionary ..)))) => true
          | _ => false
        IO.println (Json.mkObj [("commands", toJson observations), ("payload", toJson payload.totalRead),
          ("bytes", toJson (state.execution.output.toList.map UInt8.toNat)), ("oldRefuses", toJson refuses)]).compress
        return 0
  throw (IO.userError "command test-driver fuel exhausted")
