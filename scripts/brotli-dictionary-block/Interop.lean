module

import Lean
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Defs
import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs

open Lean Silmaril.Formats.Compression Silmaril.Formats.Compression.Brotli
open Execute.DistanceSwitch (BlockError)
open Execute.DistanceSwitch.Dictionary (readBlock)

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error reason => throw (IO.userError (reprStr reason))
  | .ok value => pure value

private def failure (error : BlockError) : Json :=
  let (index, kind, cause) : Option Nat × String × String := match error with
    | .initialOutput _ => (none, "initialOutput", "")
    | .fuel index _ => (some index, "fuel", "")
    | .command index reason =>
      match reason with
      | .copy _ .metaBlockExtent => (some index, "copy", "metaBlockExtent")
      | .copy _ .outputLimit => (some index, "copy", "outputLimit")
      | .distance _ .extraBitLimit => (some index, "distance", "extraBitLimit")
      | .distance _ .truncatedExtra => (some index, "distance", "truncatedExtra")
      | _ => (some index, "command", reprStr reason)
  Json.mkObj [("index", toJson index), ("kind", toJson kind), ("cause", toJson cause), ("bit", toJson error.bit)]

private def runJson (run : BlockTypes.Switch.Run) : Json := toJson [run.current, run.previous, run.remaining]

public def main (args : List String) : IO UInt32 := do
  let [path, outputArg, bitsArg, commandArg] := args | return 2
  let (some output, some bitCap, some commands) := (outputArg.toNat?, bitsArg.toNat?, commandArg.toNat?) | return 2
  let bytes ← IO.FS.readBinFile path
  let wire := bytes.data.toList
  let (window, atFrame) ← requireIO (Brotli.Internal.readWindow (Brotli.Internal.start wire))
  let (frame, tables) ← requireIO (Stream.Internal.readHeader atFrame)
  let .compressed true length := frame | throw (IO.userError "expected a final compressed fixture")
  let (header, payload) ← requireIO (CompressedHeader.read ⟨17408, 768, 8 * bytes.size - tables.totalRead⟩ tables)
  match readBlock header window length.size commands ⟨output, bitCap - payload.totalRead⟩ Execute.State.start payload with
  | .error error =>
    IO.println (Json.mkObj [("failure", failure error)]).compress
  | .ok (state, after) =>
    let ring := state.execution.ring
    let nextByte := (after.readBits ((8 - after.totalRead % 8) % 8) >>= fun (_, aligned) =>
      aligned.readBits 8).map Prod.fst
    let original := Execute.DistanceSwitch.readBlock header window length.size ⟨output, 8 * bytes.size⟩
      Execute.State.start payload
    let oldRefuses := match original with
      | .error (.command _ (.copy _ (.unsupportedDictionary ..))) => true
      | _ => false
    IO.println (Json.mkObj [("bytes", toJson (state.execution.output.toList.map UInt8.toNat)),
      ("payload", toJson payload.totalRead), ("end", toJson after.totalRead),
      ("ring", toJson [ring.latest, ring.second, ring.third, ring.fourth]),
      ("runs", toJson [runJson state.runs.literal, runJson state.runs.insertCopy, runJson state.runs.distance]),
      ("nextByte", toJson nextByte), ("oldRefuses", toJson oldRefuses)]).compress
  return 0
